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
use float::small::{CopyToSmall, Limbs, Mpfr, LIMBS_IN_SMALL_FLOAT};
use gmp_mpfr_sys::mpfr;
use std::mem;
use std::ops::Deref;
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
#[repr(C)]
pub struct SmallComplex {
    re: Mpfr,
    im: Mpfr,
    // real part is first in limbs if re.d <= im.d
    first_limbs: Limbs,
    last_limbs: Limbs,
}

impl Clone for SmallComplex {
    #[inline]
    fn clone(&self) -> SmallComplex {
        let (first_limbs, last_limbs) = if self.re_is_first() {
            (&self.first_limbs, &self.last_limbs)
        } else {
            (&self.last_limbs, &self.first_limbs)
        };
        SmallComplex {
            re: Mpfr {
                prec: self.re.prec,
                sign: self.re.sign,
                exp: self.re.exp,
                d: Default::default(),
            },
            im: Mpfr {
                prec: self.im.prec,
                sign: self.im.sign,
                exp: self.im.exp,
                d: Default::default(),
            },
            first_limbs: first_limbs.clone(),
            last_limbs: last_limbs.clone(),
        }
    }
}

impl SmallComplex {
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

    fn re_is_first(&self) -> bool {
        (self.re.d.load(Ordering::Relaxed) as usize)
            <= (self.im.d.load(Ordering::Relaxed) as usize)
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
        let first = &self.first_limbs[0] as *const _ as *mut _;
        let last = &self.last_limbs[0] as *const _ as *mut _;
        let (re_d, im_d) = if self.re_is_first() {
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

impl<Re> From<Re> for SmallComplex
where
    SmallFloat: From<Re>,
{
    fn from(src: Re) -> Self {
        let re = SmallFloat::from(src);
        let mut im: SmallFloat = unsafe { mem::uninitialized() };
        unsafe {
            xmpfr::custom_zero(
                &mut im.inner as *mut Mpfr as *mut _,
                &mut im.limbs[0],
                re.inner.prec,
            );
        }
        SmallComplex {
            re: Mpfr {
                prec: re.inner.prec,
                sign: re.inner.sign,
                exp: re.inner.exp,
                d: Default::default(),
            },
            im: Mpfr {
                prec: im.inner.prec,
                sign: im.inner.sign,
                exp: im.inner.exp,
                d: Default::default(),
            },
            first_limbs: re.limbs,
            last_limbs: [0; LIMBS_IN_SMALL_FLOAT],
        }
    }
}

impl<Re, Im> From<(Re, Im)> for SmallComplex
where
    SmallFloat: From<Re> + From<Im>,
{
    fn from(src: (Re, Im)) -> Self {
        let re = SmallFloat::from(src.0);
        let im = SmallFloat::from(src.1);
        SmallComplex {
            re: Mpfr {
                prec: re.inner.prec,
                sign: re.inner.sign,
                exp: re.inner.exp,
                d: Default::default(),
            },
            im: Mpfr {
                prec: im.inner.prec,
                sign: im.inner.sign,
                exp: im.inner.exp,
                d: Default::default(),
            },
            first_limbs: re.limbs,
            last_limbs: im.limbs,
        }
    }
}

macro_rules! impl_assign_re_im {
    ($Re: ty; $($Im: ty)*) => { $(
        impl Assign<($Re, $Im)> for SmallComplex {
            #[inline]
            fn assign(&mut self, src: ($Re, $Im)) {
                src.0.copy(&mut self.re, &mut self.first_limbs);
                src.1.copy(&mut self.im, &mut self.last_limbs);
            }
        }

    )* };
}

macro_rules! impl_assign_re {
    ($($Re: ty)*) => { $(
        impl Assign<($Re)> for SmallComplex {
            #[inline]
            fn assign(&mut self, src: $Re) {
                src.copy(&mut self.re, &mut self.first_limbs);
                unsafe {
                    xmpfr::custom_zero(
                        &mut self.im as *mut Mpfr as *mut _,
                        &mut self.last_limbs[0],
                        self.re.prec,
                    );
                }
            }
        }

        impl_assign_re_im! {
            $Re; i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64
        }
    )* };
}

impl_assign_re! { i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 }

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
