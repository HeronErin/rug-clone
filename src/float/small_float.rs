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
/// a reference to a `Float`. The `SmallFloat` will have a precision
/// according to the type of the primitive used to set its value.
///
/// * `i8`, `u8`: the `SmallFloat` will have eight bits of precision.
///
/// * `i16`, `u16`: the `SmallFloat` will have 16 bits of precision.
///
/// * `i32`, `u32`: the `SmallFloat` will have 32 bits of precision.
///
/// * `i64`, `u64`: the `SmallFloat` will have 64 bits of precision.
///
/// * `f32`: the `SmallFloat` will have 24 bits of precision.
///
/// * `f64`: the `SmallFloat` will have 53 bits of precision.
///
/// The `SmallFloat` type can be coerced to a `Float`, as it
/// implements `Deref` with a `Float` target.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::SmallFloat;
/// // `a` requires a heap allocation, has 53-bit precision
/// let mut a = Float::from((250, 53));
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

const LIMBS_IN_SMALL_FLOAT: usize = 64 / gmp::LIMB_BITS as usize;

#[repr(C)]
pub struct Mpfr {
    prec: mpfr::prec_t,
    sign: c_int,
    exp: mpfr::exp_t,
    d: AtomicPtr<gmp::limb_t>,
}

impl Default for SmallFloat {
    fn default() -> SmallFloat {
        SmallFloat::new()
    }
}

impl SmallFloat {
    /// Creates a `SmallFloat` with value 0.
    pub fn new() -> SmallFloat {
        unsafe {
            let mut ret = SmallFloat {
                inner: mem::uninitialized(),
                limbs: [0; LIMBS_IN_SMALL_FLOAT],
            };
            mpfr::custom_init(&mut ret.limbs[0] as *mut _ as *mut _, 64);
            mpfr::custom_init_set(
                &mut ret.inner as *mut _ as *mut _,
                mpfr::ZERO_KIND,
                0,
                64,
                &mut ret.limbs[0] as *mut _ as *mut _,
            );
            ret
        }
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
    fn from(val: T) -> SmallFloat {
        let mut ret = SmallFloat::new();
        ret.assign(val);
        ret
    }
}

macro_rules! assign_i {
    { $I:ty => $U:ty } => {
        impl Assign<$I> for SmallFloat {
            fn assign(&mut self, val: $I) {
                self.assign(val.wrapping_abs() as $U);
                if val < 0 {
                    unsafe {
                        mpfr::neg(
                            &mut self.inner as *mut _ as *mut _,
                            &self.inner as *const _ as *const _,
                            rraw(Round::Nearest),
                        );
                    }
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
            fn assign(&mut self, val: $U) {
                let ptr = &mut self.inner as *mut _ as *mut _;
                let limb_ptr = &mut self.limbs[0] as *mut _ as *mut _;
                unsafe {
                    mpfr::custom_init(limb_ptr, $bits);
                }
                if val == 0 {
                    unsafe {
                        mpfr::custom_init_set(
                            ptr,
                            mpfr::ZERO_KIND,
                            0,
                            $bits,
                            limb_ptr,
                        );
                    }
                    return;
                }
                let leading = val.leading_zeros();
                assert!(gmp::LIMB_BITS == 64 || gmp::LIMB_BITS == 32);
                let limb_leading = leading + gmp::LIMB_BITS as u32 - $bits;
                self.limbs[0] = (val as gmp::limb_t) << limb_leading;
                unsafe {
                    mpfr::custom_init_set(
                        ptr,
                        mpfr::REGULAR_KIND,
                        ($bits - leading) as _,
                        $bits,
                        limb_ptr,
                    );
                }
            }
        }
    };
}

assign_u_single_limb! { u8 => 8 }
assign_u_single_limb! { u16 => 16 }
assign_u_single_limb! { u32 => 32 }

impl Assign<u64> for SmallFloat {
    fn assign(&mut self, val: u64) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        let limb_ptr = &mut self.limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 64);
        }
        if val == 0 {
            unsafe {
                mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 64, limb_ptr);
            }
            return;
        }
        let leading = val.leading_zeros();
        match gmp::LIMB_BITS {
            64 => {
                self.limbs[0] = (val as gmp::limb_t) << leading;
            }
            32 => {
                let sval = val << leading;
                self.limbs[0] = sval as u32 as gmp::limb_t;
                self.limbs[1 + 0] = (sval >> 32) as u32 as gmp::limb_t;
            }
            _ => unimplemented!(),
        }
        unsafe {
            mpfr::custom_init_set(
                ptr,
                mpfr::REGULAR_KIND,
                (64 - leading) as _,
                64,
                limb_ptr,
            );
        }
    }
}

impl Assign<f32> for SmallFloat {
    fn assign(&mut self, val: f32) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        let limb_ptr = &mut self.limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 24);
            mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 24, limb_ptr);
            mpfr::set_d(ptr, val as f64, rraw(Round::Nearest));
        }
    }
}

impl Assign<f64> for SmallFloat {
    fn assign(&mut self, val: f64) {
        let ptr = &mut self.inner as *mut _ as *mut _;
        let limb_ptr = &mut self.limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 53);
            mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 53, limb_ptr);
            mpfr::set_d(ptr, val as f64, rraw(Round::Nearest));
        }
    }
}

fn rraw(round: Round) -> mpfr::rnd_t {
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}
