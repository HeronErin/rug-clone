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
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use misc::NegAbs;
use std::{i32, u32};
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A small float that does not require any memory allocation.
///
/// This can be useful when you have a primitive number type but need
/// a reference to a [`Float`](../struct.Float.html). The `SmallFloat`
/// will have a precision according to the type of the primitive used
/// to set its value.
///
/// * `i8`, `u8`: the `SmallFloat` will have eight bits of precision.
/// * `i16`, `u16`: the `SmallFloat` will have 16 bits of precision.
/// * `i32`, `u32`: the `SmallFloat` will have 32 bits of precision.
/// * `i64`, `u64`: the `SmallFloat` will have 64 bits of precision.
/// * `isize`, `usize`: the `SmallFloat` will have 32 or 64 bits of
///   precision, depending on the platform.
/// * `f32`: the `SmallFloat` will have 24 bits of precision.
/// * `f64`: the `SmallFloat` will have 53 bits of precision.
///
/// The `SmallFloat` type can be coerced to a
/// [`Float`](../struct.Float.html), as it implements
/// `Deref<Target = Float>`.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::SmallFloat;
/// // `a` requires a heap allocation, has 53-bit precision
/// let mut a = Float::with_val(53, 250);
/// // `b` can reside on the stack
/// let b = SmallFloat::from(-100f64);
/// a += &*b;
/// assert_eq!(a, 150);
/// // another computation:
/// a *= &*b;
/// assert_eq!(a, -15000);
/// ```
#[derive(Clone)]
#[repr(C)]
pub struct SmallFloat {
    pub(crate) inner: Mpfr,
    pub(crate) limbs: Limbs,
}

#[cfg(gmp_limb_bits_64)]
pub(crate) const LIMBS_IN_SMALL_FLOAT: usize = 1;
#[cfg(gmp_limb_bits_32)]
pub(crate) const LIMBS_IN_SMALL_FLOAT: usize = 2;

pub(crate) type Limbs = [gmp::limb_t; LIMBS_IN_SMALL_FLOAT];

#[repr(C)]
pub(crate) struct Mpfr {
    pub prec: mpfr::prec_t,
    pub sign: c_int,
    pub exp: mpfr::exp_t,
    pub d: AtomicPtr<gmp::limb_t>,
}

impl Clone for Mpfr {
    fn clone(&self) -> Mpfr {
        Mpfr {
            prec: self.prec,
            sign: self.sign,
            exp: self.exp,
            d: AtomicPtr::new(self.d.load(Ordering::Relaxed)),
        }
    }
}

impl SmallFloat {
    /// Returns a mutable reference to a
    /// [`Float`](../struct.Float.html) for simple operations that do
    /// not need to change the precision of the number.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to modify the precision of the
    /// referenced [`Float`](../struct.Float.html) or to swap it with
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
    #[inline]
    pub unsafe fn as_nonreallocating_float(&mut self) -> &mut Float {
        self.update_d();
        let ptr = (&mut self.inner) as *mut _ as *mut _;
        &mut *ptr
    }

    #[inline]
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpfr>(), mem::size_of::<mpfr_t>());
        // Since this is borrowed, the limb won't move around, and we
        // can set the d field.
        let d = &self.limbs[0] as *const _ as *mut _;
        self.inner.d.store(d, Ordering::Relaxed);
    }
}

impl Deref for SmallFloat {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        self.update_d();
        let ptr = (&self.inner) as *const _ as *const _;
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
            fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
                let ptr = inner as *mut Mpfr as *mut mpfr_t;
                let limbs_ptr = (&mut limbs[0]) as *mut gmp::limb_t;
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
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = inner as *mut Mpfr as *mut mpfr_t;
        let limbs_ptr = (&mut limbs[0]) as *mut gmp::limb_t;
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
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = inner as *mut Mpfr as *mut mpfr_t;
        let limbs_ptr = (&mut limbs[0]) as *mut gmp::limb_t;
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
    fn copy(self, inner: &mut Mpfr, limbs: &mut Limbs) {
        let ptr = inner as *mut Mpfr as *mut mpfr_t;
        let limbs_ptr = (&mut limbs[0]) as *mut gmp::limb_t;
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

#[inline]
fn raw_round(round: Round) -> mpfr::rnd_t {
    #[allow(deprecated)]
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}
