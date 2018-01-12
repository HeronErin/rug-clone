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
use float::Round;

use cast::cast;
use ext::mpfr as xmpfr;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
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
    inner: Mpfr,
    limbs: [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
}

#[cfg(gmp_limb_bits_64)]
pub const LIMBS_IN_SMALL_FLOAT: usize = 1;
#[cfg(gmp_limb_bits_32)]
pub const LIMBS_IN_SMALL_FLOAT: usize = 2;

// Zero prec means d is already set, so do nothing in update_d().
// This is useful for SmallComplex implementation.
#[repr(C)]
pub struct Mpfr {
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

impl Default for SmallFloat {
    #[inline]
    fn default() -> SmallFloat {
        SmallFloat::new()
    }
}

impl SmallFloat {
    /// Creates a `SmallFloat` with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::SmallFloat;
    /// let f = SmallFloat::new();
    /// // Borrow f as if it were Float.
    /// assert_eq!(*f, 0.0);
    /// ```
    #[inline]
    pub fn new() -> SmallFloat {
        unsafe {
            let mut ret = SmallFloat {
                inner: mem::uninitialized(),
                limbs: [0; LIMBS_IN_SMALL_FLOAT],
            };
            xmpfr::custom_zero(
                &mut ret.inner as *mut _ as *mut _,
                &mut ret.limbs[0],
                53,
            );
            ret
        }
    }

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

    // Zero prec means d is already set, so do nothing.
    #[inline]
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpfr>(), mem::size_of::<mpfr_t>());
        if self.inner.prec != 0 {
            // Since this is borrowed, the limb won't move around, and we
            // can set the d field.
            let d = &self.limbs[0] as *const _ as *mut _;
            self.inner.d.store(d, Ordering::Relaxed);
        }
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

macro_rules! signed {
    { $I:ty, $U:ty } => {
        impl Assign<$I> for SmallFloat {
            #[inline]
            fn assign(&mut self, val: $I) {
                self.assign(val.wrapping_abs() as $U);
                if val < 0 {
                    self.inner.sign = -1;
                }
            }
        }

        from_assign! { $I => SmallFloat }
    };
}

macro_rules! unsigned_32 {
    { $U:ty, $bits:expr } => {
        impl Assign<$U> for SmallFloat {
            fn assign(&mut self, val: $U) {
                self.update_d();
                let ptr = &mut self.inner as *mut Mpfr as *mut mpfr_t;
                let limbs = self.inner.d.load(Ordering::Relaxed);
                unsafe {
                    if val == 0 {
                        xmpfr::custom_zero(ptr, limbs, $bits);
                    } else {
                        let leading = val.leading_zeros();
                        let limb_leading
                            = leading + cast::<_, u32>(gmp::LIMB_BITS) - $bits;
                        *limbs = gmp::limb_t::from(val) << limb_leading;
                        let exp = $bits - leading;
                        xmpfr::custom_regular(ptr, limbs, cast(exp), $bits);
                    }
                }
            }
        }

        from_assign! { $U => SmallFloat }
    };
}

signed! { i8, u8 }
signed! { i16, u16 }
signed! { i32, u32 }
signed! { i64, u64 }
signed! { isize, usize }

unsigned_32! { u8, 8 }
unsigned_32! { u16, 16 }
unsigned_32! { u32, 32 }

impl Assign<u64> for SmallFloat {
    fn assign(&mut self, val: u64) {
        self.update_d();
        let ptr = &mut self.inner as *mut Mpfr as *mut mpfr_t;
        let limbs = self.inner.d.load(Ordering::Relaxed);
        unsafe {
            if val == 0 {
                xmpfr::custom_zero(ptr, limbs, 64);
            } else {
                let leading = val.leading_zeros();
                let sval = val << leading;
                #[cfg(gmp_limb_bits_64)]
                {
                    *limbs = cast(sval);
                }
                #[cfg(gmp_limb_bits_32)]
                {
                    *limbs = cast(sval as u32);
                    *limbs.offset(1) = cast((sval >> 32) as u32);
                }
                xmpfr::custom_regular(ptr, limbs, cast(64 - leading), 64);
            }
        }
    }
}

from_assign! { u64 => SmallFloat }

impl Assign<usize> for SmallFloat {
    #[inline]
    fn assign(&mut self, val: usize) {
        #[cfg(target_pointer_width = "32")]
        {
            self.assign(val as u32);
        }
        #[cfg(target_pointer_width = "64")]
        {
            self.assign(val as u64);
        }
    }
}

from_assign! { usize => SmallFloat }

impl Assign<f32> for SmallFloat {
    fn assign(&mut self, val: f32) {
        self.update_d();
        let ptr = &mut self.inner as *mut Mpfr as *mut mpfr_t;
        let limbs = self.inner.d.load(Ordering::Relaxed);
        unsafe {
            xmpfr::custom_zero(ptr, limbs, 24);
            mpfr::set_d(ptr, val.into(), raw_round(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.inner.sign = -1;
        }
    }
}

from_assign! { f32 => SmallFloat }

impl Assign<f64> for SmallFloat {
    fn assign(&mut self, val: f64) {
        self.update_d();
        let ptr = &mut self.inner as *mut Mpfr as *mut mpfr_t;
        let limbs = self.inner.d.load(Ordering::Relaxed);
        unsafe {
            xmpfr::custom_zero(ptr, limbs, 53);
            mpfr::set_d(ptr, val, raw_round(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.inner.sign = -1;
        }
    }
}

from_assign! { f64 => SmallFloat }

impl<'a> Assign<&'a SmallFloat> for SmallFloat {
    #[inline]
    fn assign(&mut self, other: &'a SmallFloat) {
        self.clone_from(other);
    }
}

impl Assign<SmallFloat> for SmallFloat {
    #[inline]
    fn assign(&mut self, other: SmallFloat) {
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
