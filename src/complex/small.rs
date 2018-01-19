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

use {Assign, Complex};

use ext::mpfr as xmpfr;
use float::SmallFloat;
use float::small::{Mpfr, LIMBS_IN_SMALL_FLOAT};
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr;
use std::mem;
use std::ops::Deref;
use std::os::raw::{c_long, c_ulong};
use std::sync::atomic::Ordering;

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
/// `Deref<Target = Complex>`.
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
#[derive(Clone)]
#[repr(C)]
pub struct SmallComplex {
    re: Mpfr,
    im: Mpfr,
    // real part is first in limbs if re.d <= im.d
    limbs: [gmp::limb_t; 2 * LIMBS_IN_SMALL_FLOAT],
}

impl Default for SmallComplex {
    fn default() -> Self {
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
    pub fn new() -> Self {
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
    ///     c.as_nonreallocating_complex().mul_i_mut(false);
    /// }
    /// assert_eq!(*c, (-3.0, 1.0));
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_complex(&mut self) -> &mut Complex {
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

impl<Re> Assign<Re> for SmallComplex
where
    SmallFloat: Assign<Re>,
{
    #[inline]
    fn assign(&mut self, re: Re) {
        const EXP_MAX: c_long = ((!0 as c_ulong) >> 1) as c_long;
        const EXP_ZERO: c_long = 0 - EXP_MAX;

        self.update_d();

        // zero prec during SmallFloat assignment so that it leaves d alone
        self.re.prec = 0;
        let re_ptr = &mut self.re as *mut Mpfr as *mut SmallFloat;
        unsafe {
            (*re_ptr).assign(re);
        }
        assert_ne!(self.re.prec, 0);

        self.im.prec = self.re.prec;
        self.im.sign = 1;
        self.im.exp = EXP_ZERO;
    }
}

impl<Re> From<Re> for SmallComplex
where
    SmallFloat: Assign<Re>,
{
    #[inline]
    fn from(val: Re) -> Self {
        let mut ret = SmallComplex::new();
        ret.assign(val);
        ret
    }
}

impl<Re, Im> Assign<(Re, Im)> for SmallComplex
where
    SmallFloat: Assign<Re> + Assign<Im>,
{
    #[inline]
    fn assign(&mut self, (re, im): (Re, Im)) {
        self.update_d();

        // zero prec during SmallFloat assignment so that it leaves d alone
        self.re.prec = 0;
        let re_ptr = &mut self.re as *mut Mpfr as *mut SmallFloat;
        unsafe {
            (*re_ptr).assign(re);
        }
        assert_ne!(self.re.prec, 0);
        self.im.prec = 0;
        let im_ptr = &mut self.im as *mut Mpfr as *mut SmallFloat;
        unsafe {
            (*im_ptr).assign(im);
        }
        assert_ne!(self.im.prec, 0);
    }
}

impl<Re, Im> From<(Re, Im)> for SmallComplex
where
    SmallFloat: Assign<Re> + Assign<Im>,
{
    #[inline]
    fn from(val: (Re, Im)) -> Self {
        let mut ret = SmallComplex::new();
        ret.assign(val);
        ret
    }
}

impl<'a> Assign<&'a Self> for SmallComplex {
    #[inline]
    fn assign(&mut self, other: &'a Self) {
        self.clone_from(other);
    }
}

impl Assign for SmallComplex {
    #[inline]
    fn assign(&mut self, other: Self) {
        mem::drop(mem::replace(self, other));
    }
}
