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

use Assign;
use Complex;
use float::Round;

use ext::mpfr as xmpfr;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A small complex number that does not require any memory
/// allocation.
///
/// This can be useful when you have real and imaginary numbers that
/// are primitive integers or floats and you need a reference to a
/// [`Complex`](../struct.Complex.html). The `SmallComplex` will have
/// a precision according to the type of the primitive used to set its
/// value.
///
/// * `i8`, `u8`: the `SmallComplex` will have eight bits of precision.
/// * `i16`, `u16`: the `SmallComplex` will have 16 bits of precision.
/// * `i32`, `u32`: the `SmallComplex` will have 32 bits of precision.
/// * `i64`, `u64`: the `SmallComplex` will have 64 bits of precision.
/// * `f32`: the `SmallComplex` will have 24 bits of precision.
/// * `f64`: the `SmallComplex` will have 53 bits of precision.
///
/// The `SmallComplex` type can be coerced to a
/// [`Complex`](../struct.Complex.html), as it implements `Deref` with
/// a [`Complex`](../struct.Complex.html) target.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// use rug::complex::SmallComplex;
/// // `a` requires a heap allocation
/// let mut a = Complex::with_val(53, (1, 2));
/// // `b` can reside on the stack
/// let b = SmallComplex::from((-10f64, -20.5f64));
/// a += &*b;
/// assert_eq!(*a.real(), -9);
/// assert_eq!(*a.imag(), -18.5);
/// ```
#[repr(C)]
pub struct SmallComplex {
    re: Mpfr,
    im: Mpfr,
    // real part is first in limbs if re.d <= im.d
    limbs: [gmp::limb_t; 2 * LIMBS_IN_SMALL_FLOAT],
}

#[cfg(gmp_limb_bits_64)]
const LIMBS_IN_SMALL_FLOAT: usize = 1;
#[cfg(gmp_limb_bits_32)]
const LIMBS_IN_SMALL_FLOAT: usize = 2;

#[repr(C)]
struct Mpfr {
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::SmallComplex;
    /// let c = SmallComplex::new();
    /// // Use c as if it were Complex.
    /// assert_eq!(*c.real(), 0.0);
    /// assert_eq!(*c.imag(), 0.0);
    /// ```
    pub fn new() -> SmallComplex {
        unsafe {
            let mut ret = SmallComplex {
                re: mem::uninitialized(),
                im: mem::uninitialized(),
                limbs: [0; 2 * LIMBS_IN_SMALL_FLOAT],
            };
            xmpfr::custom_zero(
                &mut ret.re as *mut _ as *mut _,
                &mut ret.limbs[0],
                64,
            );
            xmpfr::custom_zero(
                &mut ret.im as *mut _ as *mut _,
                &mut ret.limbs[LIMBS_IN_SMALL_FLOAT],
                64,
            );
            ret
        }
    }

    /// Returns a mutable reference to a
    /// [`Complex`](../struct.Complex.html) number for simple
    /// operations that do not need to change the precision of the
    /// real or imaginary part.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to modify the precision of the
    /// referenced [`Complex`](../struct.Complex.html) number or to
    /// swap it with another number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::SmallComplex;
    /// let mut c = SmallComplex::from((1.0f32, 3.0f32));
    /// // rotation does not change the precision
    /// unsafe {
    ///     c.as_nongrowing_mut().mul_i_mut(false);
    /// }
    /// assert_eq!(*c, (-3.0, 1.0));
    /// ```
    #[inline]
    pub unsafe fn as_nongrowing_mut(&mut self) -> &mut Complex {
        self.update_d();
        let ptr = (&mut self.re) as *mut _ as *mut _;
        &mut *ptr
    }

    // To be used when offsetting re and im in case the struct has
    // been displaced in memory; if currently re.d <= im.d then re.d
    // points to limbs[0] and im.d points to
    // limbs[LIMBS_IN_SMALL_FLOAT], otherwise re.d points to
    // limbs[LIMBS_IN_SMALL_FLOAT] and im.d points to limbs[0].
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpfr>(), mem::size_of::<mpfr::mpfr_t>());
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let first = &self.limbs[0] as *const _ as *mut _;
        let last = &self.limbs[LIMBS_IN_SMALL_FLOAT] as *const _ as *mut _;
        let re_is_first = (self.re.d.load(Ordering::Relaxed) as usize)
            <= (self.im.d.load(Ordering::Relaxed) as usize);
        let (re_d, im_d) = if re_is_first {
            (first, last)
        } else {
            (last, first)
        };
        self.re.d.store(re_d, Ordering::Relaxed);
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
    fn set_part(&mut self, limbs: *mut gmp::limb_t, t: T);
}

macro_rules! set_part_i {
    { $I:ty => $U:ty } => {
        impl SetPart<$I> for Mpfr {
            fn set_part(&mut self, limbs: *mut gmp::limb_t, val: $I) {
                self.set_part(limbs, val.wrapping_abs() as $U);
                if val < 0 {
                    self.sign = -1;
                }
            }
        }
    };
}

set_part_i! { i8 => u8 }
set_part_i! { i16 => u16 }
set_part_i! { i32 => u32 }
set_part_i! { i64 => u64 }

macro_rules! set_part_u_single_limb {
    { $U:ty => $bits:expr } => {
        impl SetPart<$U> for Mpfr {
            fn set_part(&mut self, limbs: *mut gmp::limb_t, val: $U) {
                let ptr = self as *mut _ as *mut _;
                unsafe {
                    if val == 0 {
                        xmpfr::custom_zero(ptr, limbs, $bits);
                    } else {
                        let leading = val.leading_zeros();
                        let limb_leading
                            = leading + gmp::LIMB_BITS as u32 - $bits;
                        *limbs = gmp::limb_t::from(val) << limb_leading;
                        let exp = $bits - leading;
                        xmpfr::custom_regular(ptr, limbs, exp as _, $bits);
                    }
                }
            }
        }
    };
}

set_part_u_single_limb! { u8 => 8 }
set_part_u_single_limb! { u16 => 16 }
set_part_u_single_limb! { u32 => 32 }

impl SetPart<u64> for Mpfr {
    fn set_part(&mut self, limbs: *mut gmp::limb_t, val: u64) {
        let ptr = self as *mut _ as *mut _;
        unsafe {
            if val == 0 {
                xmpfr::custom_zero(ptr, limbs, 64);
            } else {
                let leading = val.leading_zeros();
                let sval = val << leading;
                #[cfg(gmp_limb_bits_64)]
                {
                    *limbs = sval.into();
                }
                #[cfg(gmp_limb_bits_32)]
                {
                    *limbs = (sval as u32).into();
                    *limbs.offset(1) = ((sval >> 32) as u32).into();
                }
                xmpfr::custom_regular(ptr, limbs, (64 - leading) as _, 64);
            }
        }
    }
}

impl SetPart<f32> for Mpfr {
    fn set_part(&mut self, limbs: *mut gmp::limb_t, val: f32) {
        let ptr = self as *mut _ as *mut _;
        unsafe {
            xmpfr::custom_zero(ptr, limbs, 24);
            mpfr::set_d(ptr, val.into(), rraw(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.sign = -1;
        }
    }
}

impl SetPart<f64> for Mpfr {
    fn set_part(&mut self, limbs: *mut gmp::limb_t, val: f64) {
        let ptr = self as *mut _ as *mut _;
        unsafe {
            xmpfr::custom_zero(ptr, limbs, 53);
            mpfr::set_d(ptr, val, rraw(Round::Nearest));
        }
        // retain sign in case of NaN
        if val.is_sign_negative() {
            self.sign = -1;
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
                self.re.set_part(&mut self.limbs[0], re);
                self.im.set_part(&mut self.limbs[LIMBS_IN_SMALL_FLOAT], im);
            }
        }
    };
}

small_assign_re! { i8 }
small_assign_re! { i16 }
small_assign_re! { i32 }
small_assign_re! { i64 }
small_assign_re! { u8 }
small_assign_re! { u16 }
small_assign_re! { u32 }
small_assign_re! { u64 }
small_assign_re_im! { i8, i8 }
small_assign_re_im! { i16, i16 }
small_assign_re_im! { i32, i32 }
small_assign_re_im! { i64, i64 }
small_assign_re_im! { i8, u8 }
small_assign_re_im! { i16, u16 }
small_assign_re_im! { i32, u32 }
small_assign_re_im! { i64, u64 }
small_assign_re_im! { u8, i8 }
small_assign_re_im! { u16, i16 }
small_assign_re_im! { u32, i32 }
small_assign_re_im! { u64, i64 }
small_assign_re_im! { u8, u8 }
small_assign_re_im! { u16, u16 }
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
