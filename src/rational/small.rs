// Copyright © 2016–2018 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <http://www.gnu.org/licenses/>.

use {Assign, Rational};

use cast::cast;
use gmp_mpfr_sys::gmp;
use inner::InnerMut;
use integer::SmallInteger;
use integer::small::{Mpz, LIMBS_IN_SMALL_INTEGER};
use std::mem;
use std::ops::Deref;
use std::sync::atomic::Ordering;

/// A small rational number that does not require any memory
/// allocation.
///
/// This can be useful when you have a numerator and denominator that
/// are primitive integer-types such as `i64` or `u8`, and you need a
/// reference to a [`Rational`](../struct.Rational.html).
///
/// Although no allocation is required, setting the value of a
/// `SmallRational` does require some computation, as the numerator
/// and denominator need to be canonicalized.
///
/// The `SmallRational` type can be coerced to a
/// [`Rational`](../struct.Rational.html), as it implements
/// `Deref<Target = Rational>`.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
/// use rug::rational::SmallRational;
/// // `a` requires a heap allocation
/// let mut a = Rational::from((100, 13));
/// // `b` can reside on the stack
/// let b = SmallRational::from((-100, 21));
/// a /= &*b;
/// assert_eq!(*a.numer(), -21);
/// assert_eq!(*a.denom(), 13);
/// ```
#[derive(Clone)]
#[repr(C)]
pub struct SmallRational {
    num: Mpz,
    den: Mpz,
    // numerator is first in limbs if num.d <= den.d
    limbs: [gmp::limb_t; 2 * LIMBS_IN_SMALL_INTEGER],
}

impl Default for SmallRational {
    #[inline]
    fn default() -> SmallRational {
        SmallRational::new()
    }
}

impl SmallRational {
    /// Creates a `SmallRational` with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let r = SmallRational::new();
    /// // Use r as if it were Rational.
    /// assert_eq!(*r.numer(), 0);
    /// assert_eq!(*r.denom(), 1);
    /// ```
    #[inline]
    pub fn new() -> SmallRational {
        let mut ret = SmallRational {
            num: Mpz {
                size: 0,
                alloc: cast(LIMBS_IN_SMALL_INTEGER),
                d: Default::default(),
            },
            den: Mpz {
                size: 1,
                alloc: cast(LIMBS_IN_SMALL_INTEGER),
                d: Default::default(),
            },
            limbs: [0; 2 * LIMBS_IN_SMALL_INTEGER],
        };
        ret.limbs[LIMBS_IN_SMALL_INTEGER] = 1;
        ret
    }

    /// Returns a mutable reference to a
    /// [`Rational`](../struct.Rational.html) number for simple
    /// operations that do not need to allocate more space for the
    /// numerator or denominator.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to perform operations that
    /// reallocate the internal data of the referenced
    /// [`Rational`](../struct.Rational.html) number or to swap it
    /// with another number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let mut r = SmallRational::from((-15i32, 47i32));
    /// let num_capacity = r.numer().capacity();
    /// let den_capacity = r.denom().capacity();
    /// // reciprocating this will not require reallocations
    /// unsafe {
    ///     r.as_nonreallocating_rational().recip_mut();
    /// }
    /// assert_eq!(*r, (-47, 15));
    /// assert_eq!(r.numer().capacity(), num_capacity);
    /// assert_eq!(r.denom().capacity(), den_capacity);
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_rational(&mut self) -> &mut Rational {
        self.update_d();
        let ptr = (&mut self.num) as *mut _ as *mut _;
        &mut *ptr
    }

    /// Creates a `SmallRational` from a numerator and denominator,
    /// assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This method leads to undefined behaviour if `den` is zero or
    /// if `num` and `den` have common factors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// let from_unsafe = unsafe {
    ///     SmallRational::from_canonical(-13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    pub unsafe fn from_canonical<Num, Den>(num: Num, den: Den) -> SmallRational
    where
        SmallInteger: Assign<Num> + Assign<Den>,
    {
        let mut ret = SmallRational::new();
        ret.update_d();

        // zero alloc during SmallInteger assignment so that it leaves d alone
        ret.num.alloc = 0;
        let num_ptr = &mut ret.num as *mut Mpz as *mut SmallInteger;
        (*num_ptr).assign(num);
        ret.num.alloc = cast(LIMBS_IN_SMALL_INTEGER);
        ret.den.alloc = 0;
        let den_ptr = &mut ret.den as *mut Mpz as *mut SmallInteger;
        (*den_ptr).assign(den);
        ret.den.alloc = cast(LIMBS_IN_SMALL_INTEGER);

        ret
    }

    /// Creates a `SmallRational` from a 32-bit numerator and
    /// denominator, assuming they are in canonical form.
    #[deprecated(since = "0.9.2",
                 note = "use `from_canonical` instead; for example \
                         `SmallRational::from_cananoicalized_32(true, 13, 10)` \
                         can be replaced with \
                         `SmallRational::from_canonical(-13, 10)`.")]
    #[inline]
    pub unsafe fn from_canonicalized_32(
        neg: bool,
        num: u32,
        den: u32,
    ) -> SmallRational {
        let mut ret = SmallRational::from_canonical(num, den);
        if neg {
            ret.num.size = -ret.num.size;
        }
        ret
    }

    /// Creates a `SmallRational` from a 64-bit numerator and
    /// denominator, assuming they are in canonical form.
    #[deprecated(since = "0.9.2",
                 note = "use `from_canonical` instead; for example \
                         `SmallRational::from_cananoicalized_64(true, 13, 10)` \
                         can be replaced with \
                         `SmallRational::from_canonical(-13, 10)`.")]
    #[inline]
    pub unsafe fn from_canonicalized_64(
        neg: bool,
        num: u64,
        den: u64,
    ) -> SmallRational {
        let mut ret = SmallRational::from_canonical(num, den);
        if neg {
            ret.num.size = -ret.num.size;
        }
        ret
    }

    /// Sets a `SmallRational` to a 32-bit numerator and denominator,
    /// assuming they are in canonical form.
    #[deprecated(
        since = "0.9.2",
        note =
            "use `as_nonreallocating_rational` and `assign_canonical` instead; \
             for example `r.assign_canonicalized_32(true, 13u32, 10u32)` can \
             be replaced with \
             `r.as_nonreallocating_rational().assign_canonical(-13i32, 10u32)`."
    )]
    #[inline]
    pub unsafe fn assign_canonicalized_32(
        &mut self,
        neg: bool,
        num: u32,
        den: u32,
    ) {
        self.as_nonreallocating_rational()
            .assign_canonical(num, den);
        if neg {
            self.num.size = -self.num.size;
        }
    }

    /// Sets a `SmallRational` to a 64-bit numerator and denominator,
    /// assuming they are in canonical form.
    #[deprecated(
        since = "0.9.2",
        note =
            "use `as_nonreallocating_rational` and `assign_canonical` instead; \
             for example `r.assign_canonicalized_32(true, 13u64, 10u64)` can \
             be replaced with \
             `r.as_nonreallocating_rational().assign_canonical(-13i64, 10u64)`."
    )]
    #[inline]
    pub unsafe fn assign_canonicalized_64(
        &mut self,
        neg: bool,
        num: u64,
        den: u64,
    ) {
        self.as_nonreallocating_rational()
            .assign_canonical(num, den);
        if neg {
            self.num.size = -self.num.size;
        }
    }

    // To be used when offsetting num and den in case the struct has
    // been displaced in memory; if currently num.d <= den.d then
    // num.d points to limbs[0] and den.d points to
    // limbs[LIMBS_IN_SMALL_INTEGER], otherwise num.d points to
    // limbs[LIMBS_IN_SMALL_INTEGER] and den.d points to limbs[0].
    #[inline]
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpz>(), mem::size_of::<gmp::mpz_t>());
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let first = &self.limbs[0] as *const _ as *mut _;
        let last = &self.limbs[LIMBS_IN_SMALL_INTEGER] as *const _ as *mut _;
        let num_is_first = (self.num.d.load(Ordering::Relaxed) as usize)
            <= (self.den.d.load(Ordering::Relaxed) as usize);
        let (num_d, den_d) = if num_is_first {
            (first, last)
        } else {
            (last, first)
        };
        self.num.d.store(num_d, Ordering::Relaxed);
        self.den.d.store(den_d, Ordering::Relaxed);
    }
}

impl Deref for SmallRational {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        self.update_d();
        let ptr = (&self.num) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<Num> Assign<Num> for SmallRational
where
    SmallInteger: Assign<Num>,
{
    #[inline]
    fn assign(&mut self, num: Num) {
        self.update_d();

        // zero alloc during SmallInteger assignment so that it leaves d alone
        self.num.alloc = 0;
        let num_ptr = &mut self.num as *mut Mpz as *mut SmallInteger;
        unsafe {
            (*num_ptr).assign(num);
        }
        self.num.alloc = cast(LIMBS_IN_SMALL_INTEGER);

        self.den.size = 1;
        unsafe {
            *self.den.d.load(Ordering::Relaxed) = 1;
        }
    }
}

impl<Num> From<Num> for SmallRational
where
    SmallInteger: Assign<Num>,
{
    #[inline]
    fn from(val: Num) -> Self {
        let mut ret = SmallRational::new();
        ret.assign(val);
        ret
    }
}

impl<Num, Den> Assign<(Num, Den)> for SmallRational
where
    SmallInteger: Assign<Num> + Assign<Den>,
{
    #[inline]
    fn assign(&mut self, (num, den): (Num, Den)) {
        self.update_d();

        // zero alloc during SmallInteger assignment so that it leaves d alone
        self.num.alloc = 0;
        let num_ptr = &mut self.num as *mut Mpz as *mut SmallInteger;
        unsafe {
            (*num_ptr).assign(num);
        }
        self.num.alloc = cast(LIMBS_IN_SMALL_INTEGER);
        self.den.alloc = 0;
        let den_ptr = &mut self.den as *mut Mpz as *mut SmallInteger;
        unsafe {
            (*den_ptr).assign(den);
        }
        self.den.alloc = cast(LIMBS_IN_SMALL_INTEGER);

        unsafe {
            assert_ne!(
                *self.den.d.load(Ordering::Relaxed),
                0,
                "division by zero"
            );
            gmp::mpq_canonicalize(
                self.as_nonreallocating_rational().inner_mut(),
            );
        }
    }
}

impl<Num, Den> From<(Num, Den)> for SmallRational
where
    SmallInteger: Assign<Num> + Assign<Den>,
{
    #[inline]
    fn from(val: (Num, Den)) -> Self {
        let mut ret = SmallRational::new();
        ret.assign(val);
        ret
    }
}

impl<'a> Assign<&'a SmallRational> for SmallRational {
    #[inline]
    fn assign(&mut self, other: &'a SmallRational) {
        self.clone_from(other);
    }
}

impl Assign<SmallRational> for SmallRational {
    #[inline]
    fn assign(&mut self, other: SmallRational) {
        mem::drop(mem::replace(self, other));
    }
}
