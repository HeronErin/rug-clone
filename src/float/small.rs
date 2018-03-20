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

use {Assign, Float};
use cast::cast;
use ext::mpfr as xmpfr;
use float::Round;
use float::big::raw_round;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use misc::NegAbs;
use std::{i32, u32};
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/**
A small float that does not require any memory allocation.

This can be useful when you have a primitive number type but need a
reference to a [`Float`]. The `SmallFloat` will have a precision
according to the type of the primitive used to set its value.

* [`i8`], [`u8`]: the `SmallFloat` will have eight bits of precision.
* [`i16`], [`u16`]: the `SmallFloat` will have 16 bits of precision.
* [`i32`], [`u32`]: the `SmallFloat` will have 32 bits of precision.
* [`i64`], [`u64`]: the `SmallFloat` will have 64 bits of precision.
* [`isize`], [`usize`]: the `SmallFloat` will have 32 or 64 bits of
  precision, depending on the platform.
* [`f32`]: the `SmallFloat` will have 24 bits of precision.
* [`f64`]: the `SmallFloat` will have 53 bits of precision.

The `SmallFloat` type can be coerced to a [`Float`], as it implements
[`Deref<Target = Float>`][`Deref`].

# Examples

```rust
use rug::Float;
use rug::float::SmallFloat;
// `a` requires a heap allocation, has 53-bit precision
let mut a = Float::with_val(53, 250);
// `b` can reside on the stack
let b = SmallFloat::from(-100f64);
a += &*b;
assert_eq!(a, 150);
// another computation:
a *= &*b;
assert_eq!(a, -15000);
```

[`Deref`]: https://doc.rust-lang.org/std/ops/trait.Deref.html
[`Float`]: ../struct.Float.html
[`f32`]: https://doc.rust-lang.org/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/std/primitive.f64.html
[`i16`]: https://doc.rust-lang.org/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/std/primitive.isize.html
[`u16`]: https://doc.rust-lang.org/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/std/primitive.usize.html
*/
#[derive(Clone)]
#[repr(C)]
pub struct SmallFloat {
    pub(crate) inner: Mpfr,
    pub(crate) limbs: Limbs,
}

pub(crate) const LIMBS_IN_SMALL_FLOAT: usize = (64 / gmp::LIMB_BITS) as usize;
pub(crate) type Limbs = [gmp::limb_t; LIMBS_IN_SMALL_FLOAT];

#[repr(C)]
pub(crate) struct Mpfr {
    pub prec: mpfr::prec_t,
    pub sign: c_int,
    pub exp: mpfr::exp_t,
    pub d: AtomicPtr<gmp::limb_t>,
}

fn _static_assertions() {
    static_assert_size!(Limbs: 8);
    static_assert_size!(Mpfr, mpfr_t);
}

// Mpfr is only used inside SmallFloat and SmallComplex. The d field
// does not need to be copied from self. SmallComplex::clone is
// responsible to keep real and imag parts ordered.
impl Clone for Mpfr {
    #[inline]
    fn clone(&self) -> Mpfr {
        Mpfr {
            prec: self.prec,
            sign: self.sign,
            exp: self.exp,
            d: Default::default(),
        }
    }
}

impl SmallFloat {
    /// Returns a mutable reference to a [`Float`] for simple
    /// operations that do not need to change the precision of the
    /// number.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to modify the precision of the
    /// referenced [`Float`] or to swap it with
    /// another number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::SmallFloat;
    /// let mut f = SmallFloat::from(1.0f32);
    /// // addition does not change the precision
    /// unsafe {
    ///     *f.as_nonreallocating_float() += 2.0;
    /// }
    /// assert_eq!(*f, 3.0);
    /// ```
    ///
    /// [`Float`]: ../struct.Float.html
    #[inline]
    pub unsafe fn as_nonreallocating_float(&mut self) -> &mut Float {
        self.update_d();
        let ptr = cast_ptr_mut!(&mut self.inner, Float);
        &mut *ptr
    }

    #[inline]
    fn update_d(&self) {
        // Since this is borrowed, the limb won't move around, and we
        // can set the d field.
        let d = &self.limbs[0] as *const gmp::limb_t as *mut gmp::limb_t;
        self.inner.d.store(d, Ordering::Relaxed);
    }
}

impl Deref for SmallFloat {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        self.update_d();
        let ptr = cast_ptr!(&self.inner, Float);
        unsafe { &*ptr }
    }
}

pub(crate) trait CopyToSmall: Copy {
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs);
}

macro_rules! signed {
    ($($I: ty)*) => { $(
        impl CopyToSmall for $I {
            #[inline]
            fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
                let (neg, abs) = self.neg_abs();
                abs.copy(inner, limbs);
                if neg {
                    inner.sign = -1;
                }
            }
        }
    )* };
}

macro_rules! unsigned_32 {
    ($U: ty, $bits: expr) => {
        impl CopyToSmall for $U {
            #[inline]
            fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
                let ptr = cast_ptr_mut!(inner, mpfr_t);
                let limbs_ptr: *mut gmp::limb_t = &mut limbs[0];
                unsafe {
                    if self == 0 {
                        xmpfr::custom_zero(ptr, limbs_ptr, $bits);
                    } else {
                        let leading = self.leading_zeros();
                        let limb_leading =
                            leading + cast::<_, u32>(gmp::LIMB_BITS) - $bits;
                        limbs[0] = gmp::limb_t::from(self) << limb_leading;
                        let exp = $bits - leading;
                        xmpfr::custom_regular(ptr, limbs_ptr, cast(exp), $bits);
                    }
                }
            }
        }
    };
}

signed! { i8 i16 i32 i64 isize }

unsigned_32! { u8, 8 }
unsigned_32! { u16, 16 }
unsigned_32! { u32, 32 }

impl CopyToSmall for u64 {
    #[inline]
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr: *mut gmp::limb_t = &mut limbs[0];
        unsafe {
            if self == 0 {
                xmpfr::custom_zero(ptr, limbs_ptr, 64);
            } else {
                let leading = self.leading_zeros();
                let sval = self << leading;
                #[cfg(gmp_limb_bits_64)]
                {
                    limbs[0] = sval;
                }
                #[cfg(gmp_limb_bits_32)]
                {
                    limbs[0] = sval as u32;
                    limbs[1] = (sval >> 32) as u32;
                }
                xmpfr::custom_regular(ptr, limbs_ptr, cast(64 - leading), 64);
            }
        }
    }
}

impl CopyToSmall for usize {
    #[inline]
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        #[cfg(target_pointer_width = "32")]
        {
            (self as u32).copy(inner, limbs);
        }
        #[cfg(target_pointer_width = "64")]
        {
            (self as u64).copy(inner, limbs);
        }
    }
}

impl CopyToSmall for f32 {
    #[inline]
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr: *mut gmp::limb_t = &mut limbs[0];
        unsafe {
            xmpfr::custom_zero(ptr, limbs_ptr, 24);
            mpfr::set_d(ptr, self.into(), raw_round(Round::Nearest));
        }
        // retain sign in case of NaN
        if self.is_sign_negative() {
            inner.sign = -1;
        }
    }
}

impl CopyToSmall for f64 {
    #[inline]
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = cast_ptr_mut!(inner, mpfr_t);
        let limbs_ptr: *mut gmp::limb_t = &mut limbs[0];
        unsafe {
            xmpfr::custom_zero(ptr, limbs_ptr, 53);
            mpfr::set_d(ptr, self, raw_round(Round::Nearest));
        }
        // retain sign in case of NaN
        if self.is_sign_negative() {
            inner.sign = -1;
        }
    }
}

macro_rules! impl_assign_from {
    ($($T: ty)*) => { $(
        impl Assign<$T> for SmallFloat {
            #[inline]
            fn assign(&mut self, src: $T) {
                src.copy(&mut self.inner, &mut self.limbs);
            }
        }

        impl From<$T> for SmallFloat {
            #[inline]
            fn from(src: $T) -> Self {
                let mut dst = SmallFloat {
                    inner: unsafe { mem::uninitialized() },
                    limbs: [0; LIMBS_IN_SMALL_FLOAT],
                };
                src.copy(&mut dst.inner, &mut dst.limbs);
                dst
            }
        }
    )* };
}

impl_assign_from! { i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 }

impl<'a> Assign<&'a Self> for SmallFloat {
    #[inline]
    fn assign(&mut self, other: &'a Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallFloat {
    #[inline]
    fn assign(&mut self, other: Self) {
        mem::drop(mem::replace(self, other));
    }
}
