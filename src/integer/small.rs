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

use {Assign, Integer};

use cast::cast;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use misc::NegAbs;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/**
A small integer that does not require any memory allocation.

This can be useful when you have a primitive integer type such as
[`u64`] or [`i8`], but need a reference to an [`Integer`].

If there are functions that take a [`u32`] or [`i32`] directly instead
of an [`Integer`] reference, using them can still be faster than using
a `SmallInteger`; the functions would still need to check for the size
of an [`Integer`] obtained using `SmallInteger`.

The `SmallInteger` type can be coerced to an [`Integer`], as it
implements [`Deref<Target = Integer>`][`Deref`].

# Examples

```rust
use rug::integer::SmallInteger;
use rug::Integer;
// `a` requires a heap allocation
let mut a = Integer::from(250);
// `b` can reside on the stack
let b = SmallInteger::from(-100);
a.lcm_mut(&b);
assert_eq!(a, 500);
// another computation:
a.lcm_mut(&SmallInteger::from(30));
assert_eq!(a, 1500);
```

[`Deref`]: https://doc.rust-lang.org/nightly/std/ops/trait.Deref.html
[`Integer`]: ../struct.Integer.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
*/
#[derive(Clone)]
#[repr(C)]
pub struct SmallInteger {
    pub(crate) inner: Mpz,
    pub(crate) limbs: Limbs,
}

#[cfg(not(int_128))]
pub(crate) const LIMBS_IN_SMALL_INTEGER: usize = (64 / gmp::LIMB_BITS) as usize;
#[cfg(int_128)]
pub(crate) const LIMBS_IN_SMALL_INTEGER: usize =
    (128 / gmp::LIMB_BITS) as usize;
pub(crate) type Limbs = [gmp::limb_t; LIMBS_IN_SMALL_INTEGER];

#[repr(C)]
pub(crate) struct Mpz {
    pub alloc: c_int,
    pub size: c_int,
    pub d: AtomicPtr<gmp::limb_t>,
}

fn _static_assertions() {
    #[cfg(not(int_128))]
    static_assert_size!(Limbs: 8);
    #[cfg(int_128)]
    static_assert_size!(Limbs: 16);
    static_assert_size!(Mpz, mpz_t);
}

// Mpz is only used inside SmallInteger and SmallRational. The only
// field that needs to be actually copied from self is size.
// SmallRational::clone is responsible to keep num and den ordered.
impl Clone for Mpz {
    #[inline]
    fn clone(&self) -> Mpz {
        Mpz {
            alloc: cast(LIMBS_IN_SMALL_INTEGER),
            size: self.size,
            d: Default::default(),
        }
    }
}

impl Default for SmallInteger {
    #[inline]
    fn default() -> Self {
        SmallInteger::new()
    }
}

impl SmallInteger {
    /// Creates a [`SmallInteger`] with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::SmallInteger;
    /// let i = SmallInteger::new();
    /// // Borrow i as if it were Integer.
    /// assert_eq!(*i, 0);
    /// ```
    ///
    /// [`SmallInteger`]: struct.SmallInteger.html
    #[inline]
    pub fn new() -> Self {
        SmallInteger {
            inner: Mpz {
                alloc: cast(LIMBS_IN_SMALL_INTEGER),
                size: 0,
                d: Default::default(),
            },
            limbs: [0; LIMBS_IN_SMALL_INTEGER],
        }
    }

    /// Returns a mutable reference to an [`Integer`] for simple
    /// operations that do not need to allocate more space for the
    /// number.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to perform operations that
    /// reallocate the internal data of the referenced [`Integer`] or
    /// to swap it with another number.
    ///
    /// Some GMP functions swap the allocations of their target
    /// operands; calling such functions with the mutable reference
    /// returned by this method can lead to undefined behaviour.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::SmallInteger;
    /// use rug::Assign;
    /// let mut i = SmallInteger::from(1u64);
    /// let capacity = i.capacity();
    /// // another u64 will not require a reallocation
    /// unsafe {
    ///     i.as_nonreallocating_integer().assign(2u64);
    /// }
    /// assert_eq!(*i, 2);
    /// assert_eq!(i.capacity(), capacity);
    /// ```
    ///
    /// [`Integer`]: ../struct.Integer.html
    #[inline]
    pub unsafe fn as_nonreallocating_integer(&mut self) -> &mut Integer {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Integer);
        &mut *ptr
    }

    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d field.
        let d = &self.limbs[0] as *const gmp::limb_t as *mut gmp::limb_t;
        self.inner.d.store(d, Ordering::Relaxed);
    }
}

impl Deref for SmallInteger {
    type Target = Integer;
    #[inline]
    fn deref(&self) -> &Integer {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Integer);
        unsafe { &*ptr }
    }
}

pub(crate) trait CopyToSmall: Copy {
    fn copy(self, size: &mut c_int, limbs: &mut Limbs);
}

macro_rules! signed {
    ($($I:ty)*) => { $(
        impl CopyToSmall for $I {
            #[inline]
            fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
                let (neg, abs) = self.neg_abs();
                abs.copy(size, limbs);
                if neg {
                    *size = -*size;
                }
            }
        }
    )* };
}

macro_rules! one_limb {
    ($($U:ty)*) => { $(
        impl CopyToSmall for $U {
            #[inline]
            fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
                if self == 0 {
                    *size = 0;
                } else {
                    *size = 1;
                    limbs[0] = self.into();
                }
            }
        }
    )* };
}

signed! { i8 i16 i32 i64 }
#[cfg(int_128)]
signed! { i128 }
signed! { isize }
one_limb! { u8 u16 u32 }

#[cfg(gmp_limb_bits_64)]
one_limb! { u64 }

#[cfg(gmp_limb_bits_32)]
impl CopyToSmall for u64 {
    #[inline]
    fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
        if self == 0 {
            *size = 0;
        } else if self <= 0xffff_ffff {
            *size = 1;
            limbs[0] = self as u32;
        } else {
            *size = 2;
            limbs[0] = self as u32;
            limbs[1] = (self >> 32) as u32;
        }
    }
}

#[cfg(all(int_128, gmp_limb_bits_64))]
impl CopyToSmall for u128 {
    #[inline]
    fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
        if self == 0 {
            *size = 0;
        } else if self <= 0xffff_ffff_ffff_ffff {
            *size = 1;
            limbs[0] = self as u64;
        } else {
            *size = 2;
            limbs[0] = self as u64;
            limbs[1] = (self >> 64) as u64;
        }
    }
}

#[cfg(all(int_128, gmp_limb_bits_32))]
impl CopyToSmall for u128 {
    #[inline]
    fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
        if self == 0 {
            *size = 0;
        } else if self <= 0xffff_ffff {
            *size = 1;
            limbs[0] = self as u32;
        } else if self <= 0xffff_ffff_ffff_ffff {
            *size = 2;
            limbs[0] = self as u32;
            limbs[1] = (self >> 32) as u32;
        } else if self <= 0xffff_ffff_ffff_ffff_ffff_ffff {
            *size = 3;
            limbs[0] = self as u32;
            limbs[1] = (self >> 32) as u32;
            limbs[2] = (self >> 64) as u32;
        } else {
            *size = 4;
            limbs[0] = self as u32;
            limbs[1] = (self >> 32) as u32;
            limbs[2] = (self >> 64) as u32;
            limbs[3] = (self >> 96) as u32;
        }
    }
}

impl CopyToSmall for usize {
    #[inline]
    fn copy(self, size: &mut c_int, limbs: &mut Limbs) {
        #[cfg(target_pointer_width = "32")]
        {
            (self as u32).copy(size, limbs);
        }
        #[cfg(target_pointer_width = "64")]
        {
            (self as u64).copy(size, limbs);
        }
    }
}

macro_rules! impl_assign_from {
    ($($T:ty)*) => { $(
        impl Assign<$T> for SmallInteger {
            #[inline]
            fn assign(&mut self, src: $T) {
                src.copy(&mut self.inner.size, &mut self.limbs);
            }
        }

        from_assign! { $T => SmallInteger }
    )* };
}

impl_assign_from! { i8 i16 i32 i64 }
#[cfg(int_128)]
impl_assign_from! { i128 }
impl_assign_from! { isize }
impl_assign_from! { u8 u16 u32 u64 }
#[cfg(int_128)]
impl_assign_from! { u128 }
impl_assign_from! { usize }

impl<'a> Assign<&'a Self> for SmallInteger {
    #[inline]
    fn assign(&mut self, other: &Self) {
        self.clone_from(other);
    }
}

impl<'a> Assign for SmallInteger {
    #[inline]
    fn assign(&mut self, other: Self) {
        mem::drop(mem::replace(self, other));
    }
}

#[cfg(test)]
mod tests {
    use integer::SmallInteger;
    use Assign;

    #[test]
    fn check_assign() {
        let mut i = SmallInteger::from(-1i32);
        assert_eq!(*i, -1);
        let other = SmallInteger::from(2i32);
        i.assign(&other);
        assert_eq!(*i, 2);
        i.assign(6u8);
        assert_eq!(*i, 6);
        i.assign(-6i8);
        assert_eq!(*i, -6);
        i.assign(other);
        assert_eq!(*i, 2);
        i.assign(6u16);
        assert_eq!(*i, 6);
        i.assign(-6i16);
        assert_eq!(*i, -6);
        i.assign(6u32);
        assert_eq!(*i, 6);
        i.assign(-6i32);
        assert_eq!(*i, -6);
        i.assign(0xf_0000_0006u64);
        assert_eq!(*i, 0xf_0000_0006u64);
        i.assign(-0xf_0000_0006i64);
        assert_eq!(*i, -0xf_0000_0006i64);
        #[cfg(int_128)]
        {
            i.assign(6u128 << 64 | 7u128);
            assert_eq!(*i, 6u128 << 64 | 7u128);
            i.assign(-6i128 << 64 | 7i128);
            assert_eq!(*i, -6i128 << 64 | 7i128);
        }
        i.assign(6usize);
        assert_eq!(*i, 6);
        i.assign(-6isize);
        assert_eq!(*i, -6);
        i.assign(0u32);
        assert_eq!(*i, 0);
    }
}
