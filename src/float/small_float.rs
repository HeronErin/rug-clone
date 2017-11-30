// Copyright © 2017 University of Malta

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

use ext::mpfr as xmpfr;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use std::{i32, u32};
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

#[repr(C)]
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
/// * `f32`: the `SmallFloat` will have 24 bits of precision.
/// * `f64`: the `SmallFloat` will have 53 bits of precision.
///
/// The `SmallFloat` type can be coerced to a
/// [`Float`](../struct.Float.html), as it implements `Deref` with a
/// [`Float`](../struct.Float.html) target.
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
pub struct SmallFloat {
    inner: Mpfr,
    limbs: [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
}

#[cfg(gmp_limb_bits_64)]
const LIMBS_IN_SMALL_FLOAT: usize = 1;
#[cfg(gmp_limb_bits_32)]
const LIMBS_IN_SMALL_FLOAT: usize = 2;

#[repr(C)]
pub struct Mpfr {
    prec: mpfr::prec_t,
    sign: c_int,
    exp: mpfr::exp_t,
    d: AtomicPtr<gmp::limb_t>,
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
                64,
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
    ///     *f.as_nongrowing_mut() += 2.0;
    /// }
    /// assert_eq!(*f, 3.0);
    /// ```
    #[inline]
    pub unsafe fn as_nongrowing_mut(&mut self) -> &mut Float {
        self.update_d();
        let ptr = (&mut self.inner) as *mut _ as *mut _;
        &mut *ptr
    }

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

impl<T> From<T> for SmallFloat
where
    SmallFloat: Assign<T>,
{
    #[inline]
    fn from(val: T) -> SmallFloat {
        let mut ret = SmallFloat::new();
        ret.assign(val);
        ret
    }
}

macro_rules! assign_i {
    { $I:ty => $U:ty } => {
        impl Assign<$I> for SmallFloat {
            #[inline]
            fn assign(&mut self, val: $I) {
                self.assign(val.wrapping_abs() as $U);
                if val < 0 {
                    self.inner.sign = -1;
                }
            }
        }
    };
}

assign_i! { i8 => u8 }
assign_i! { i16 => u16 }
assign_i! { i32 => u32 }
assign_i! { i64 => u64 }

macro_rules! assign_u_single_limb {
    { $U:ty => $bits:expr } => {
        impl Assign<$U> for SmallFloat {
            #[inline]
            fn assign(&mut self, val: $U) {
                let ptr = &mut self.inner as *mut _ as *mut _;
                unsafe {
                    if val == 0 {
                        xmpfr::custom_zero(ptr, &mut self.limbs[0], $bits);
                    } else {
                        let leading = val.leading_zeros();
                        let limb_leading
                            = leading + gmp::LIMB_BITS as u32 - $bits;
                        self.limbs[0] = gmp::limb_t::from(val) << limb_leading;
                        let limbs = &mut self.limbs[0];
                        let exp = $bits - leading;
                        xmpfr::custom_regular(ptr, limbs, exp as _, $bits);
                    }
                }
            }
        }
    };
}

assign_u_single_limb! { u8 => 8 }
assign_u_single_limb! { u16 => 16 }
assign_u_single_limb! { u32 => 32 }

impl Assign<u64> for SmallFloat {
    #[inline]
    fn assign(&mut self, val: u64) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        unsafe {
            if val == 0 {
                xmpfr::custom_zero(ptr, &mut self.limbs[0], 64);
            } else {
                let leading = val.leading_zeros();
                let sval = val << leading;
                #[cfg(gmp_limb_bits_64)]
                {
                    self.limbs[0] = sval.into();
                }
                #[cfg(gmp_limb_bits_32)]
                {
                    self.limbs[0] = (sval as u32).into();
                    self.limbs[1] = ((sval >> 32) as u32).into();
                }
                let limbs = &mut self.limbs[0];
                xmpfr::custom_regular(ptr, limbs, (64 - leading) as _, 64);
            }
        }
    }
}

impl Assign<f32> for SmallFloat {
    #[inline]
    fn assign(&mut self, val: f32) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        unsafe {
            xmpfr::custom_zero(ptr, &mut self.limbs[0], 24);
            mpfr::set_d(ptr, val.into(), rraw(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.inner.sign = -1;
        }
    }
}

impl Assign<f64> for SmallFloat {
    #[inline]
    fn assign(&mut self, val: f64) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        unsafe {
            xmpfr::custom_zero(ptr, &mut self.limbs[0], 53);
            mpfr::set_d(ptr, val as f64, rraw(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.inner.sign = -1;
        }
    }
}

#[inline]
fn rraw(round: Round) -> mpfr::rnd_t {
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}
