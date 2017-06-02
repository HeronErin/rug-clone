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

use Complex;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr;
use rugflo::Round;
use rugint::Assign;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

#[repr(C)]
/// A small complex number that does not require any memory
/// allocation.
///
/// This can be useful when you have real and imaginary numbers that
/// are 32-bit or 64-bit integers or floats and you need a reference
/// to a `Complex`.
///
/// The `SmallComplex` type can be coerced to a `Complex`, as it
/// implements `Deref` with a `Complex` target.
///
/// # Examples
///
/// ```rust
/// use rugcom::{Complex, SmallComplex};
/// // `a` requires a heap allocation
/// let mut a = Complex::from(((1, 2), 53));
/// // `b` can reside on the stack
/// let b = SmallComplex::from((-10f64, -20.5f64));
/// a += &*b;
/// assert_eq!(*a.real(), -9);
/// assert_eq!(*a.imag(), -18.5);
/// ```
pub struct SmallComplex {
    re: Mpfr,
    im: Mpfr,
    re_limbs: [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
    im_limbs: [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
}

const LIMBS_IN_SMALL_FLOAT: usize = 64 / gmp::LIMB_BITS as usize;

#[repr(C)]
pub struct Mpfr {
    prec: mpfr::prec_t,
    sign: c_int,
    exp: mpfr::exp_t,
    d: AtomicPtr<gmp::limb_t>,
}

impl Default for SmallComplex {
    fn default() -> SmallComplex {
        SmallComplex::new()
    }
}

impl SmallComplex {
    /// Creates a `SmallComplex` with value 0.
    pub fn new() -> SmallComplex {
        unsafe {
            let mut ret = SmallComplex {
                re: mem::uninitialized(),
                im: mem::uninitialized(),
                re_limbs: [0; LIMBS_IN_SMALL_FLOAT],
                im_limbs: [0; LIMBS_IN_SMALL_FLOAT],
            };
            mpfr::custom_init(&mut ret.re_limbs[0] as *mut _ as *mut _, 64);
            mpfr::custom_init_set(
                &mut ret.re as *mut _ as *mut _,
                mpfr::ZERO_KIND,
                0,
                64,
                &mut ret.re_limbs[0] as *mut _ as *mut _,
            );
            mpfr::custom_init(&mut ret.im_limbs[0] as *mut _ as *mut _, 64);
            mpfr::custom_init_set(
                &mut ret.im as *mut _ as *mut _,
                mpfr::ZERO_KIND,
                0,
                64,
                &mut ret.im_limbs[0] as *mut _ as *mut _,
            );
            ret
        }
    }

    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpfr>(), mem::size_of::<mpfr::mpfr_t>());
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let re_d = &self.re_limbs[0] as *const _ as *mut _;
        self.re.d.store(re_d, Ordering::Relaxed);
        let im_d = &self.im_limbs[0] as *const _ as *mut _;
        self.im.d.store(im_d, Ordering::Relaxed);
    }
}

impl Deref for SmallComplex {
    type Target = Complex;
    fn deref(&self) -> &Complex {
        self.update_d();
        let ptr = (&self.re) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<T> From<T> for SmallComplex
where
    SmallComplex: Assign<T>,
{
    fn from(val: T) -> SmallComplex {
        let mut ret = SmallComplex::new();
        ret.assign(val);
        ret
    }
}

trait SetPart<T> {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        t: T,
    );
}

impl SetPart<i32> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: i32,
    ) {
        self.set_part(limbs, val.wrapping_abs() as u32);
        if val < 0 {
            unsafe {
                mpfr::neg(
                    self as *mut _ as *mut _,
                    self as *const _ as *const _,
                    rraw(Round::Nearest),
                );
            }
        }
    }
}

impl SetPart<i64> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: i64,
    ) {
        self.set_part(limbs, val.wrapping_abs() as u64);
        if val < 0 {
            unsafe {
                mpfr::neg(
                    self as *mut _ as *mut _,
                    self as *const _ as *const _,
                    rraw(Round::Nearest),
                );
            }
        }
    }
}

impl SetPart<u32> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: u32,
    ) {
        let ptr = self as *mut _ as *mut _;
        let limb_ptr = &mut limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 32);
        }
        if val == 0 {
            unsafe {
                mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 32, limb_ptr);
            }
            return;
        }
        let leading = val.leading_zeros();
        match gmp::LIMB_BITS {
            64 | 32 => {
                let limb_leading = leading + gmp::LIMB_BITS as u32 - 32;
                limbs[0] = (val as gmp::limb_t) << limb_leading;
            }
            _ => unreachable!(),
        }
        unsafe {
            mpfr::custom_init_set(
                ptr,
                mpfr::REGULAR_KIND,
                (32 - leading) as _,
                32,
                limb_ptr,
            );
        }
    }
}

impl SetPart<u64> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: u64,
    ) {
        let ptr = self as *mut _ as *mut _;
        let limb_ptr = &mut limbs[0] as *mut _ as *mut _;
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
                limbs[0] = (val as gmp::limb_t) << leading;
            }
            32 => {
                let sval = val << leading;
                limbs[0] = sval as u32 as gmp::limb_t;
                limbs[1 + 0] = (sval >> 32) as u32 as gmp::limb_t;
            }
            _ => unreachable!(),
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

impl SetPart<f32> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: f32,
    ) {
        let ptr = self as *mut _ as *mut _;
        let limb_ptr = &mut limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 24);
            mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 24, limb_ptr);
            mpfr::set_d(ptr, val as f64, rraw(Round::Nearest));
        }
    }
}

impl SetPart<f64> for Mpfr {
    fn set_part(
        &mut self,
        limbs: &mut [gmp::limb_t; LIMBS_IN_SMALL_FLOAT],
        val: f64,
    ) {
        let ptr = self as *mut _ as *mut _;
        let limb_ptr = &mut limbs[0] as *mut _ as *mut _;
        unsafe {
            mpfr::custom_init(limb_ptr, 53);
            mpfr::custom_init_set(ptr, mpfr::ZERO_KIND, 0, 53, limb_ptr);
            mpfr::set_d(ptr, val, rraw(Round::Nearest));
        }
    }
}

macro_rules! small_assign_re {
    { $T:ty } => {
        impl Assign<$T> for SmallComplex {
            fn assign(&mut self, val: $T) {
                self.assign((val, 0 as $T));
            }
        }
    };
}

macro_rules! small_assign_re_im {
    { $R:ty, $I:ty } => {
        impl Assign<($R, $I)> for SmallComplex {
            fn assign(&mut self, (re, im): ($R, $I)) {
                self.re.set_part(&mut self.re_limbs, re);
                self.im.set_part(&mut self.im_limbs, im);
            }
        }
    };
}

small_assign_re! { i32 }
small_assign_re! { i64 }
small_assign_re! { u32 }
small_assign_re! { u64 }
small_assign_re_im! { i32, i32 }
small_assign_re_im! { i64, i64 }
small_assign_re_im! { i32, u32 }
small_assign_re_im! { i64, u64 }
small_assign_re_im! { u32, i32 }
small_assign_re_im! { u64, i64 }
small_assign_re_im! { u32, u32 }
small_assign_re_im! { u64, u64 }

small_assign_re! { f32 }
small_assign_re! { f64 }
small_assign_re_im! { f32, f32 }
small_assign_re_im! { f64, f64 }

fn rraw(round: Round) -> mpfr::rnd_t {
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}
