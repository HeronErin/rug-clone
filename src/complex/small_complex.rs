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
/// [`Complex`](../struct.Complex.html).
///
/// The `SmallComplex` will have a precision according to the types of
/// the primitives used to set its real and imaginary parts. Note that
/// if different types are used to set the parts, the parts can have
/// different precisions.
///
/// * `i8`, `u8`: the part will have eight bits of precision.
/// * `i16`, `u16`: the part will have 16 bits of precision.
/// * `i32`, `u32`: the part will have 32 bits of precision.
/// * `i64`, `u64`: the part will have 64 bits of precision.
/// * `isize`, `usize`: the part will have 32 or 64 bits of precision,
///   depending on the platform.
/// * `f32`: the part will have 24 bits of precision.
/// * `f64`: the part will have 53 bits of precision.
///
/// The `SmallComplex` type can be coerced to a
/// [`Complex`](../struct.Complex.html), as it implements
/// `Deref<Complex>`.
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
                53,
            );
            xmpfr::custom_zero(
                &mut ret.im as *mut _ as *mut _,
                &mut ret.limbs[LIMBS_IN_SMALL_FLOAT],
                53,
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
    ///     c.as_nonreallocating_mut().mul_i_mut(false);
    /// }
    /// assert_eq!(*c, (-3.0, 1.0));
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_mut(&mut self) -> &mut Complex {
        self.update_d();
        let ptr = (&mut self.re) as *mut _ as *mut _;
        &mut *ptr
    }

    // To be used when offsetting re and im in case the struct has
    // been displaced in memory; if currently re.d <= im.d then re.d
    // points to limbs[0] and im.d points to
    // limbs[LIMBS_IN_SMALL_FLOAT], otherwise re.d points to
    // limbs[LIMBS_IN_SMALL_FLOAT] and im.d points to limbs[0].
    #[inline]
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
    #[inline]
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
    #[inline]
    fn from(val: T) -> Self {
        let mut ret = SmallComplex::new();
        ret.assign(val);
        ret
    }
}

trait SetPart<T> {
    fn set_part(&mut self, limbs: *mut gmp::limb_t, t: T);
}

macro_rules! signed_part {
    { $I:ty, $U:ty } => {
        impl SetPart<$I> for Mpfr {
            #[inline]
            fn set_part(&mut self, limbs: *mut gmp::limb_t, val: $I) {
                self.set_part(limbs, val.wrapping_abs() as $U);
                if val < 0 {
                    self.sign = -1;
                }
            }
        }
    };
}

signed_part! { i8, u8 }
signed_part! { i16, u16 }
signed_part! { i32, u32 }
signed_part! { i64, u64 }
signed_part! { isize, usize }

macro_rules! unsigned_32_part {
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

unsigned_32_part! { u8 => 8 }
unsigned_32_part! { u16 => 16 }
unsigned_32_part! { u32 => 32 }

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

impl SetPart<usize> for Mpfr {
    fn set_part(&mut self, limbs: *mut gmp::limb_t, val: usize) {
        #[cfg(target_pointer_width = "32")]
        {
            self.set_part(limbs, val as u32);
        }
        #[cfg(target_pointer_width = "64")]
        {
            self.set_part(limbs, val as u64);
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

macro_rules! cross {
    { $Re:ty, $Im:ty } => {
        impl Assign<($Re, $Im)> for SmallComplex {
            #[inline]
            fn assign(&mut self, val: ($Re, $Im)) {
                self.re.set_part(&mut self.limbs[0], val.0);
                self.im.set_part(&mut self.limbs[LIMBS_IN_SMALL_FLOAT], val.1);
            }
        }
    }
}

// (Major), (Major, Major), (Major, Minor*), (Minor*, Major)
macro_rules! matrix {
    { $Major:ty $(; $Minor:ty)* } => {
        impl Assign<$Major> for SmallComplex {
            #[inline]
            fn assign(&mut self, val: $Major) {
                self.re.set_part(&mut self.limbs[0], val);
                self.im.set_part(
                    &mut self.limbs[LIMBS_IN_SMALL_FLOAT],
                    0 as $Major,
                );
            }
        }
        cross! { $Major, $Major }
        $( cross! { $Major, $Minor } )*
        $( cross! { $Minor, $Major } )*
    }
}

matrix! { u8 }
matrix! { i8; u8 }
matrix! { u16; i8; u8 }
matrix! { i16; u16; i8; u8 }
matrix! { u32; i16; u16; i8; u8 }
matrix! { i32; u32; i16; u16; i8; u8 }
matrix! { usize; i32; u32; i16; u16; i8; u8 }
matrix! { isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { i64; u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { f32; i64; u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { f64; f32; i64; u64; isize; usize; i32; u32; i16; u16; i8; u8 }

fn rraw(round: Round) -> mpfr::rnd_t {
    #[allow(deprecated)]
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}
