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
use integer::small::{CopyToSmall, Limbs, Mpz, LIMBS_IN_SMALL_INTEGER};
use std::mem;
use std::ops::Deref;
use std::sync::atomic::Ordering;

/**
A small rational number that does not require any memory allocation.

This can be useful when you have a numerator and denominator that are
primitive integer-types such as [`i64`] or [`u8`], and you need a
reference to a [`Rational`].

Although no allocation is required, setting the value of a
`SmallRational` does require some computation, as the numerator and
denominator need to be canonicalized.

The `SmallRational` type can be coerced to a [`Rational`], as it
implements [`Deref<Target = Rational>`][`Deref`].

# Examples

```rust
use rug::Rational;
use rug::rational::SmallRational;
// `a` requires a heap allocation
let mut a = Rational::from((100, 13));
// `b` can reside on the stack
let b = SmallRational::from((-100, 21));
a /= &*b;
assert_eq!(*a.numer(), -21);
assert_eq!(*a.denom(), 13);
```

[`Deref`]: https://doc.rust-lang.org/nightly/std/ops/trait.Deref.html
[`Rational`]: ../struct.Rational.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
*/
#[repr(C)]
pub struct SmallRational {
    inner: Mpq,
    // numerator is first in limbs if inner.num.d <= inner.den.d
    first_limbs: Limbs,
    last_limbs: Limbs,
}

impl Clone for SmallRational {
    #[inline]
    fn clone(&self) -> SmallRational {
        let (first_limbs, last_limbs) = if self.num_is_first() {
            (&self.first_limbs, &self.last_limbs)
        } else {
            (&self.last_limbs, &self.first_limbs)
        };
        SmallRational {
            inner: self.inner.clone(),
            first_limbs: *first_limbs,
            last_limbs: *last_limbs,
        }
    }
}

#[derive(Clone)]
#[repr(C)]
struct Mpq {
    num: Mpz,
    den: Mpz,
}

fn _static_assertions() {
    static_assert_size!(Mpq, gmp::mpq_t);
}

impl Default for SmallRational {
    #[inline]
    fn default() -> Self {
        SmallRational::new()
    }
}

#[cfg(all(not(int_128), gmp_limb_bits_64))]
const LIMBS_ONE: Limbs = [1];
#[cfg(all(not(int_128), gmp_limb_bits_32))]
const LIMBS_ONE: Limbs = [1, 0];
#[cfg(all(int_128, gmp_limb_bits_64))]
const LIMBS_ONE: Limbs = [1, 0];
#[cfg(all(int_128, gmp_limb_bits_32))]
const LIMBS_ONE: Limbs = [1, 0, 0, 0];

impl SmallRational {
    /// Creates a [`SmallRational`] with value 0.
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
    ///
    /// [`SmallRational`]: struct.SmallRational.html
    #[inline]
    pub fn new() -> Self {
        SmallRational {
            inner: Mpq {
                num: Mpz {
                    alloc: cast(LIMBS_IN_SMALL_INTEGER),
                    size: 0,
                    d: Default::default(),
                },
                den: Mpz {
                    alloc: cast(LIMBS_IN_SMALL_INTEGER),
                    size: 1,
                    d: Default::default(),
                },
            },
            first_limbs: [0; LIMBS_IN_SMALL_INTEGER],
            last_limbs: LIMBS_ONE,
        }
    }

    /// Returns a mutable reference to a [`Rational`] number for
    /// simple operations that do not need to allocate more space for
    /// the numerator or denominator.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to perform operations that
    /// reallocate the internal data of the referenced [`Rational`]
    /// number or to swap it with another number, although it is
    /// allowed to swap the numerator and denominator allocations,
    /// such as in the reciprocal operation [`recip_mut`].
    ///
    /// Some GMP functions swap the allocations of their target
    /// operands; calling such functions with the mutable reference
    /// returned by this method can lead to undefined behaviour.
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
    ///
    /// [`Rational`]: ../struct.Rational.html
    /// [`recip_mut`]: ../struct.Rational.html#method.recip_mut
    #[inline]
    pub unsafe fn as_nonreallocating_rational(&mut self) -> &mut Rational {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Rational);
        &mut *ptr
    }

    /// Creates a [`SmallRational`] from a numerator and denominator,
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
    ///
    /// [`SmallRational`]: struct.SmallRational.html
    pub unsafe fn from_canonical<Num, Den>(num: Num, den: Den) -> Self
    where
        SmallInteger: From<Num> + From<Den>,
    {
        let (num, den) = (SmallInteger::from(num), SmallInteger::from(den));
        SmallRational {
            inner: Mpq {
                num: num.inner.clone(),
                den: den.inner.clone(),
            },
            first_limbs: num.limbs,
            last_limbs: den.limbs,
        }
    }

    fn num_is_first(&self) -> bool {
        (self.inner.num.d.load(Ordering::Relaxed) as usize)
            <= (self.inner.den.d.load(Ordering::Relaxed) as usize)
    }

    // To be used when offsetting num and den in case the struct has
    // been displaced in memory; if currently num.d <= den.d then
    // num.d points to first_limbs and den.d points to last_limbs,
    // otherwise num.d points to last_limbs and den.d points to
    // first_limbs.
    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let first =
            &self.first_limbs[0] as *const gmp::limb_t as *mut gmp::limb_t;
        let last =
            &self.last_limbs[0] as *const gmp::limb_t as *mut gmp::limb_t;
        let (num_d, den_d) = if self.num_is_first() {
            (first, last)
        } else {
            (last, first)
        };
        self.inner.num.d.store(num_d, Ordering::Relaxed);
        self.inner.den.d.store(den_d, Ordering::Relaxed);
    }
}

impl Deref for SmallRational {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Rational);
        unsafe { &*ptr }
    }
}

impl<Num> From<Num> for SmallRational
where
    SmallInteger: From<Num>,
{
    fn from(src: Num) -> Self {
        let num = SmallInteger::from(src);
        SmallRational {
            inner: Mpq {
                num: num.inner.clone(),
                den: Mpz {
                    alloc: cast(LIMBS_IN_SMALL_INTEGER),
                    size: 1,
                    d: Default::default(),
                },
            },
            first_limbs: num.limbs,
            last_limbs: LIMBS_ONE,
        }
    }
}

impl<Num, Den> From<(Num, Den)> for SmallRational
where
    SmallInteger: From<Num> + From<Den>,
{
    fn from(src: (Num, Den)) -> Self {
        let num = SmallInteger::from(src.0);
        let den = SmallInteger::from(src.1);
        assert_ne!(den.inner.size, 0, "division by zero");
        let mut dst = SmallRational {
            inner: Mpq {
                num: num.inner.clone(),
                den: den.inner.clone(),
            },
            first_limbs: num.limbs,
            last_limbs: den.limbs,
        };
        unsafe {
            gmp::mpq_canonicalize(
                dst.as_nonreallocating_rational().inner_mut(),
            );
        }
        dst
    }
}

macro_rules! impl_assign_num_den {
    ($Num: ty; $($Den: ty)*) => { $(
        impl Assign<($Num, $Den)> for SmallRational {
            fn assign(&mut self, src: ($Num, $Den)) {
                assert_ne!(src.1, 0, "division by zero");
                {
                    let (num_limbs, den_limbs) = if self.num_is_first() {
                        (&mut self.first_limbs, &mut self.last_limbs)
                    } else {
                        (&mut self.last_limbs, &mut self.first_limbs)
                    };
                    src.0.copy(&mut self.inner.num.size, num_limbs);
                    src.1.copy(&mut self.inner.den.size, den_limbs);
                }
                unsafe {
                    gmp::mpq_canonicalize(
                        self.as_nonreallocating_rational().inner_mut(),
                    );
                }
            }
        }
    )* };
}

macro_rules! impl_assign_num {
    ($($Num: ty)*) => { $(
        impl Assign<$Num> for SmallRational {
            #[inline]
            fn assign(&mut self, src: $Num) {
                let (num_limbs, den_limbs) = if self.num_is_first() {
                    (&mut self.first_limbs, &mut self.last_limbs)
                } else {
                    (&mut self.last_limbs, &mut self.first_limbs)
                };
                src.copy(&mut self.inner.num.size, num_limbs);
                self.inner.den.size = 1;
                den_limbs[0] = 1;
            }
        }

        impl_assign_num_den! { $Num; i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        impl_assign_num_den! { $Num; i128 }
        impl_assign_num_den! { $Num; u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        impl_assign_num_den! { $Num; u128 }
    )* };
}

impl_assign_num! { i8 i16 i32 i64 isize }
#[cfg(int_128)]
impl_assign_num! { i128 }
impl_assign_num! { u8 u16 u32 u64 usize }
#[cfg(int_128)]
impl_assign_num! { u128 }

impl<'a> Assign<&'a Self> for SmallRational {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallRational {
    #[inline]
    fn assign(&mut self, other: Self) {
        mem::drop(mem::replace(self, other));
    }
}
