// Copyright © 2016–2017 University of Malta

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

use gmp_mpfr_sys::gmp;
use inner::InnerMut;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

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
/// `Deref<Rational>`.
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
#[repr(C)]
pub struct SmallRational {
    num: Mpz,
    den: Mpz,
    // numerator is first in limbs if num.d <= den.d
    limbs: [gmp::limb_t; 2 * LIMBS_IN_SMALL_INTEGER],
}

#[cfg(gmp_limb_bits_64)]
const LIMBS_IN_SMALL_INTEGER: usize = 1;
#[cfg(gmp_limb_bits_32)]
const LIMBS_IN_SMALL_INTEGER: usize = 2;

#[repr(C)]
struct Mpz {
    alloc: c_int,
    size: c_int,
    d: AtomicPtr<gmp::limb_t>,
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
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
                d: Default::default(),
            },
            den: Mpz {
                size: 1,
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
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
    ///     r.as_nonreallocating_mut().recip_mut();
    /// }
    /// assert_eq!(*r, (-47, 15));
    /// assert_eq!(r.numer().capacity(), num_capacity);
    /// assert_eq!(r.denom().capacity(), den_capacity);
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_mut(&mut self) -> &mut Rational {
        self.update_d();
        let ptr = (&mut self.num) as *mut _ as *mut _;
        &mut *ptr
    }

    /// Creates a `SmallRational` from a 32-bit numerator and
    /// denominator, assuming they are in canonical form.
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
    ///     SmallRational::from_canonicalized_32(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    #[inline]
    pub unsafe fn from_canonicalized_32(
        neg: bool,
        num: u32,
        den: u32,
    ) -> SmallRational {
        let mut ret = SmallRational::new();
        if num != 0 {
            ret.assign_canonicalized_32(neg, num, den);
        }
        ret
    }

    /// Creates a `SmallRational` from a 64-bit numerator and
    /// denominator, assuming they are in canonical form.
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
    ///     SmallRational::from_canonicalized_64(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    #[inline]
    pub unsafe fn from_canonicalized_64(
        neg: bool,
        num: u64,
        den: u64,
    ) -> SmallRational {
        let mut ret = SmallRational::new();
        if num != 0 {
            ret.assign_canonicalized_64(neg, num, den);
        }
        ret
    }

    /// Sets a `SmallRational` to a 32-bit numerator and denominator,
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
    /// let mut from_unsafe = SmallRational::new();
    /// unsafe {
    ///     from_unsafe.assign_canonicalized_32(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    #[inline]
    pub unsafe fn assign_canonicalized_32(
        &mut self,
        neg: bool,
        num: u32,
        den: u32,
    ) {
        self.num.size = if num == 0 {
            0
        } else if neg {
            -1
        } else {
            1
        };
        self.num.d = Default::default();
        self.den.size = 1;
        self.den.d = Default::default();
        self.limbs[0] = num.into();
        self.limbs[LIMBS_IN_SMALL_INTEGER] = den.into();
    }

    /// Sets a `SmallRational` to a 64-bit numerator and denominator,
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
    /// let mut from_unsafe = SmallRational::new();
    /// unsafe {
    ///     from_unsafe.assign_canonicalized_64(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    #[inline]
    pub unsafe fn assign_canonicalized_64(
        &mut self,
        neg: bool,
        num: u64,
        den: u64,
    ) {
        #[cfg(gmp_limb_bits_64)]
        {
            self.num.size = if num == 0 {
                0
            } else if neg {
                -1
            } else {
                1
            };
            self.num.d = Default::default();
            self.den.size = 1;
            self.den.d = Default::default();
            self.limbs[0] = num.into();
            self.limbs[LIMBS_IN_SMALL_INTEGER] = den.into();
        }
        #[cfg(gmp_limb_bits_32)]
        {
            if num == 0 {
                self.num.size = 0;
                self.limbs[0] = 0;
            } else if num <= 0xffff_ffff {
                self.num.size = if neg { -1 } else { 1 };
                self.limbs[0] = (num as u32).into();
            } else {
                self.num.size = if neg { -2 } else { 2 };
                self.limbs[0] = (num as u32).into();
                self.limbs[1] = ((num >> 32) as u32).into();
            }
            self.num.d = Default::default();
            if den <= 0xffff_ffff {
                self.den.size = 1;
                self.limbs[LIMBS_IN_SMALL_INTEGER] = (den as u32).into();
            } else {
                self.den.size = 2;
                self.limbs[LIMBS_IN_SMALL_INTEGER] = (den as u32).into();
                self.limbs[LIMBS_IN_SMALL_INTEGER + 1] =
                    ((den >> 32) as u32).into();
            }
            self.den.d = Default::default();
        }
    }

    #[inline]
    fn set_num_32(&mut self, neg: bool, num: u32) {
        unsafe {
            self.assign_canonicalized_32(neg, num, 1);
        }
    }

    #[inline]
    fn set_num_den_32(&mut self, neg: bool, num: u32, den: u32) {
        assert_ne!(den, 0, "division by zero");
        unsafe {
            self.assign_canonicalized_32(neg, num, den);
            gmp::mpq_canonicalize(self.as_nonreallocating_mut().inner_mut());
        }
    }

    #[inline]
    fn set_num_64(&mut self, neg: bool, num: u64) {
        unsafe {
            self.assign_canonicalized_64(neg, num, 1);
        }
    }

    #[inline]
    fn set_num_den_64(&mut self, neg: bool, num: u64, den: u64) {
        assert_ne!(den, 0, "division by zero");
        unsafe {
            self.assign_canonicalized_64(neg, num, den);
            gmp::mpq_canonicalize(self.as_nonreallocating_mut().inner_mut());
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

impl<T> From<T> for SmallRational
where
    SmallRational: Assign<T>,
{
    #[inline]
    fn from(val: T) -> Self {
        let mut ret = SmallRational::new();
        ret.assign(val);
        ret
    }
}

macro_rules! cross {
    {
        $U:ty, $method_num:ident, $method_num_den:ident;
        $NumI:ty, $NumU:ty; $DenI:ty, $DenU:ty
    } => {
        impl Assign<($NumI, $DenI)> for SmallRational {
            #[inline]
            fn assign(&mut self, val: ($NumI, $DenI)) {
                self.$method_num_den(
                    (val.0 < 0) != (val.1 < 0),
                    val.0.wrapping_abs() as $NumU as $U,
                    val.1.wrapping_abs() as $DenU as $U,
                );
            }
        }
        impl Assign<($NumI, $DenU)> for SmallRational {
            #[inline]
            fn assign(&mut self, val: ($NumI, $DenU)) {
                self.$method_num_den(
                    val.0 < 0,
                    val.0.wrapping_abs() as $NumU as $U,
                    val.1 as $U,
                );
            }
        }
        impl Assign<($NumU, $DenI)> for SmallRational {
            #[inline]
            fn assign(&mut self, val: ($NumU, $DenI)) {
                self.$method_num_den(
                    val.1 < 0,
                    val.0 as $U,
                    val.1.wrapping_abs() as $DenU as $U,
                );
            }
        }
        impl Assign<($NumU, $DenU)> for SmallRational {
            #[inline]
            fn assign(&mut self, val: ($NumU, $DenU)) {
                self.$method_num_den(false, val.0 as $U, val.1 as $U);
            }
        }
    }
}

// (Major), (Major, Major), (Major, Minor*), (Minor*, Major)
macro_rules! matrix {
    {
        $U:ty, $method_num:ident, $method_num_den:ident;
        $MajorI:ty, $MajorU:ty $(; $MinorI:ty, $MinorU:ty)*
    } => {
        impl Assign<$MajorI> for SmallRational {
            #[inline]
            fn assign(&mut self, val: $MajorI) {
                self.$method_num(val < 0, val.wrapping_abs() as $MajorU as $U);
            }
        }
        impl Assign<$MajorU> for SmallRational {
            #[inline]
            fn assign(&mut self, val: $MajorU) {
                self.$method_num(false, val as $U);
            }
        }
        cross! {
            $U, $method_num, $method_num_den;
            $MajorI, $MajorU; $MajorI, $MajorU
        }
        $( cross! {
            $U, $method_num, $method_num_den;
            $MajorI, $MajorU; $MinorI, $MinorU
        } )*
        $( cross! {
            $U, $method_num, $method_num_den;
            $MinorI, $MinorU; $MajorI, $MajorU
        } )*
    }
}

matrix! {
    u32, set_num_32, set_num_den_32;
    i8, u8
}
matrix! {
    u32, set_num_32, set_num_den_32;
    i16, u16; i8, u8
}
matrix! {
    u32, set_num_32, set_num_den_32;
    i32, u32; i16, u16; i8, u8
}
#[cfg(target_pointer_width = "32")]
matrix! {
    u32, set_num_32, set_num_den_32;
    isize, usize; i32, u32; i16, u16; i8, u8
}
#[cfg(target_pointer_width = "64")]
matrix! {
    u64, set_num_64, set_num_den_64;
    isize, usize; i32, u32; i16, u16; i8, u8
}
matrix! {
    u64, set_num_64, set_num_den_64;
    i64, u64; isize, usize; i32, u32; i16, u16; i8, u8
}
