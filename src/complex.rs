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

use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpc;
use gmp_mpfr_sys::mpfr;
#[cfg(feature = "rand")]
use rand::Rng;
use rugflo::{self, AddRound, AssignRound, DivRound, Float, FromRound, MulRound,
             PowRound, Round, ShlRound, ShrRound, SubRound};
use rugint::{Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign,
             SubFromAssign};
use rugrat::Rational;
use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_int, c_ulong};

type Prec2 = (u32, u32);

type Round2 = (Round, Round);

type Ordering2 = (Ordering, Ordering);

/// A multi-precision complex number.
/// The precision has to be set during construction.
///
/// There are two versions of most methods:
///
/// 1. The first rounds the returned or stored `Complex` number to the
///    [nearest](enum.Round.html#variant.Nearest) representable value.
/// 2. The second applies the specified [rounding
///    methods](../rugflo/enum.Round.html) for the real and imaginary parts, and
///    returns the rounding directions for both:
///    * `Ordering::Less` if the returned/stored part is less than
///      the exact result,
///    * `Ordering::Equal` if the returned/stored part is equal to
///      the exact result,
///    * `Ordering::Greater` if the returned/stored part is greater
///      than the exact result,
///
/// # Note on `Round::AwayFromZero`
///
/// For `Complex` numbers, `Round::AwayFromZero` is not implemented,
/// and trying to use it will start a panic.

pub struct Complex {
    data: mpc::mpc_t,
}

pub fn raw(q: &Complex) -> &mpc::mpc_t {
    &q.data
}

pub fn raw_mut(q: &mut Complex) -> &mut mpc::mpc_t {
    &mut q.data
}

impl Complex {
    fn real_raw(&self) -> &mpfr::mpfr_t {
        &raw(self).re
    }

    fn imag_raw(&self) -> &mpfr::mpfr_t {
        &raw(self).im
    }

    fn real_imag_raw(&self) -> (&mpfr::mpfr_t, &mpfr::mpfr_t) {
        let r = raw(self);
        (&r.re, &r.im)
    }

    fn real_raw_mut(&mut self) -> &mut mpfr::mpfr_t {
        &mut raw_mut(self).re
    }

    fn imag_raw_mut(&mut self) -> &mut mpfr::mpfr_t {
        &mut raw_mut(self).im
    }

    fn real_imag_raw_mut(&mut self) -> (&mut mpfr::mpfr_t, &mut mpfr::mpfr_t) {
        let r = raw_mut(self);
        (&mut r.re, &mut r.im)
    }
}

fn float_unraw(r: &mpfr::mpfr_t) -> &Float {
    let ptr = r as *const _ as *const Float;
    unsafe { &*ptr }
}

fn float_unraw_mut(r: &mut mpfr::mpfr_t) -> &mut Float {
    let ptr = r as *mut _ as *mut Float;
    unsafe { &mut *ptr }
}

impl Drop for Complex {
    fn drop(&mut self) {
        unsafe {
            mpc::mpc_clear(raw_mut(self));
        }
    }
}

impl Clone for Complex {
    fn clone(&self) -> Complex {
        let prec = self.prec();
        let mut ret = Complex::new(prec);
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Complex) {
        self.assign(source);
    }
}

macro_rules! math_op1 {
    { $d:expr,
      $method:ident,
      $d_round:expr,
      $method_round:ident,
      $func:path } => {
        #[doc=$d]
        pub fn $method(&mut self) -> &mut Complex {
            self.$method_round((Round::Nearest, Round::Nearest));
            self
        }

        #[doc=$d_round]
        pub fn $method_round(&mut self, round: Round2) -> Ordering2 {
            ordering2(unsafe {
                $func(raw_mut(self), raw(self), rraw2(round))
            })
        }
    };
}

impl Complex {
    /// Create a new complex number with the specified precisions for
    /// the real and imaginary parts and with value 0.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn new(prec: Prec2) -> Complex {
        assert!(prec.0 >= rugflo::prec_min() && prec.0 <= rugflo::prec_max() &&
                prec.1 >= rugflo::prec_min() &&
                prec.1 <= rugflo::prec_max(),
                "precision out of range");
        unsafe {
            let mut data: mpc::mpc_t = mem::uninitialized();
            mpc::mpc_init3(&mut data, prec.0.into(), prec.1.into());
            mpfr::mpfr_set_zero(&mut data.re, 0);
            mpfr::mpfr_set_zero(&mut data.im, 0);
            Complex { data: data }
        }
    }

    /// Returns the precision of the real and imaginary parts.
    pub fn prec(&self) -> Prec2 {
        (self.real().prec(), self.imag().prec())
    }

    /// Sets the precision of the real and imaginary parts exactly,
    /// rounding to the nearest.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn set_prec(&mut self, prec: Prec2) {
        float_unraw_mut(self.real_raw_mut()).set_prec(prec.0);
        float_unraw_mut(self.imag_raw_mut()).set_prec(prec.1);
    }

    /// Sets the precision of the real and imaginary parts exactly,
    /// applying the specified rounding method.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn set_prec_round(&mut self, prec: Prec2, round: Round2) -> Ordering2 {
        (float_unraw_mut(self.real_raw_mut()).set_prec_round(prec.0, round.0),
         float_unraw_mut(self.imag_raw_mut()).set_prec_round(prec.1, round.1))
    }

    /// Borrows the real part.
    pub fn real(&self) -> &Float {
        float_unraw(self.real_raw())
    }

    /// Borrows the imaginary part.
    pub fn imag(&self) -> &Float {
        float_unraw(self.imag_raw())
    }

    /// Borrows the real and imaginary parts.
    pub fn as_real_imag(&self) -> (&Float, &Float) {
        let (real, imag) = self.real_imag_raw();
        (float_unraw(real), float_unraw(imag))
    }

    /// Borrows the real and imaginary parts mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    ///
    /// let mut c = Complex::from(((1, 2), (53, 53)));
    /// {
    ///     let mut real_imag = c.as_mut_real_imag();
    ///     *real_imag.0 += 3;
    ///     *real_imag.1 += 4;
    ///     // borrow ends here
    /// }
    /// let (real, imag) = c.as_real_imag();
    /// assert!(*real == 4 && *imag == 6);
    /// ```
    pub fn as_mut_real_imag(&mut self) -> (&mut Float, &mut Float) {
        let (real, imag) = self.real_imag_raw_mut();
        (float_unraw_mut(real), float_unraw_mut(imag))
    }

    /// Converts `self` into real and imaginary `Float` values,
    /// consuming `self`.
    pub fn into_real_imag(self) -> (Float, Float) {
        let (mut real, mut imag) = unsafe { mem::uninitialized() };
        *float_raw_mut(&mut real) = *self.real_raw();
        *float_raw_mut(&mut imag) = *self.imag_raw();
        mem::forget(self);
        (real, imag)
    }

    math_op1! {
        "Computes a projection onto the Riemann sphere, \
         rounding to the nearest.",
        proj,
        "Computes a projection onto the Riemann sphere, \
         applying the specified rounding method.",
        proj_round,
        mpc::mpc_proj
    }
    math_op1! {
        "Computes the square, \
         rounding to the nearest.",
        square,
        "Computes the square, \
         applying the specified rounding method.",
        square_round,
        mpc::mpc_sqr
    }
    math_op1! {
        "Computes the square root, \
         rounding to the nearest.",
        sqrt,
        "Computes the square root, \
         applying the specified rounding method.",
        sqrt_round,
        mpc::mpc_sqrt
    }

    /// Computes the complex conjugate,
    /// rounding to the nearest.
    pub fn conjugate(&mut self) -> &mut Complex {
        let round = (Round::Nearest, Round::Nearest);
        unsafe {
            mpc::mpc_conj(raw_mut(self), raw(self), rraw2(round));
        }
        self
    }

    /// Computes the absolute value,
    /// rounding to the nearest.
    pub fn abs<'a>(&self, buf: &'a mut Float) -> &'a mut Float {
        self.abs_round(buf, Round::Nearest);
        buf
    }

    /// Computes the absolute value,
    /// applying the specified rounding method.
    pub fn abs_round(&self, buf: &mut Float, round: Round) -> Ordering {
        unsafe {
            mpc::mpc_abs(float_raw_mut(buf), raw(self), rraw(round)).cmp(&0)
        }
    }

    /// Computes the argument,
    /// rounding to the nearest.
    pub fn arg<'a>(&self, buf: &'a mut Float) -> &'a mut Float {
        self.arg_round(buf, Round::Nearest);
        buf
    }

    /// Computes the argument,
    /// applying the specified rounding method.
    pub fn arg_round(&self, buf: &mut Float, round: Round) -> Ordering {
        unsafe {
            mpc::mpc_arg(float_raw_mut(buf), raw(self), rraw(round)).cmp(&0)
        }
    }

    pub fn mul_i(&mut self, negative: bool, round: Round2) -> Ordering2 {
        let sgn = if negative { -1 } else { 0 };
        ordering2(unsafe {
            mpc::mpc_mul_i(raw_mut(self), raw(self), sgn, rraw2(round))
        })
    }

    /// Computes the reciprocal,
    /// rounding to the nearest.
    pub fn recip(&mut self) -> &mut Complex {
        self.recip_round((Round::Nearest, Round::Nearest));
        self
    }

    /// Computes the reciprocal,
    /// applying the specified rounding method.
    pub fn recip_round(&mut self, round: Round2) -> Ordering2 {
        ordering2(unsafe {
            mpc::mpc_ui_div(raw_mut(self), 1, raw(self), rraw2(round))
        })
    }

    /// Computes the norm, that is the square of the absolute value,
    /// rounding to the nearest.
    pub fn norm<'a>(&self, buf: &'a mut Float) -> &'a mut Float {
        self.norm_round(buf, Round::Nearest);
        buf
    }

    /// Computes the norm, that is the square of the absolute value,
    /// applying the specified rounding method.
    pub fn norm_round(&self, buf: &mut Float, round: Round) -> Ordering {
        unsafe {
            mpc::mpc_norm(float_raw_mut(buf), raw(self), rraw(round)).cmp(&0)
        }
    }

    math_op1! {
        "Computes the natural logarithm, \
         rounding to the nearest.",
        ln,
        "Computes the natural logarithm, \
         applying the specified rounding method.",
        ln_round,
        mpc::mpc_log
    }
    math_op1! {
        "Computes the logarithm to base 10, \
         rounding to the nearest.",
        log10,
        "Computes the logarithm to base 10, \
         applying the specified rounding method.",
        log10_round,
        mpc::mpc_log10
    }
    math_op1! {
        "Computes the exponential, \
         rounding to the nearest.",
        exp,
        "Computes the exponential, \
         applying the specified rounding method.",
        exp_round,
        mpc::mpc_exp
    }
    math_op1! {
        "Computes the sine, \
         rounding to the nearest.",
        sin,
        "Computes the sine, \
         applying the specified rounding method.",
        sin_round,
        mpc::mpc_sin
    }
    math_op1! {
        "Computes the cosine, \
         rounding to the nearest.",
        cos,
        "Computes the cosine, \
         applying the specified rounding method.",
        cos_round,
        mpc::mpc_cos
    }

    /// Computes the sine and cosine, rounding to the nearest. The
    /// sine is stored in `self` and keeps its precision, while the
    /// cosine is stored in `buf` keeping its precision.
    pub fn sin_cos(&mut self, buf: &mut Complex) {
        let round = (Round::Nearest, Round::Nearest);
        self.sin_cos_round(buf, round, round);
    }

    /// Computes the sine and cosine, applying the specified rounding
    /// methods. The sine is stored in `self` and keeps its precision,
    /// while the cosine is stored in `buf` keeping its precision.
    pub fn sin_cos_round(&mut self,
                         buf: &mut Complex,
                         round_sin: Round2,
                         round_cos: Round2)
                         -> (Ordering2, Ordering2) {
        let ord = unsafe {
            mpc::mpc_sin_cos(raw_mut(self),
                             raw_mut(buf),
                             raw(self),
                             rraw2(round_sin),
                             rraw2(round_cos))
        };
        (ordering2(ord & 15), ordering2(ord >> 4))
    }

    math_op1! {
        "Computes the tangent, \
         rounding to the nearest.",
        tan,
        "Computes the tangent, \
         applying the specified rounding method.",
        tan_round,
        mpc::mpc_tan
    }
    math_op1! {
        "Computes the hyperbolic sine, \
         rounding to the nearest.",
        sinh,
        "Computes the hyperboic sine, \
         applying the specified rounding method.",
        sinh_round,
        mpc::mpc_sinh
    }
    math_op1! {
        "Computes the hyperbolic cosine, \
         rounding to the nearest.",
        cosh,
        "Computes the hyperboic cosine, \
         applying the specified rounding method.",
        cosh_round,
        mpc::mpc_cosh
    }
    math_op1! {
        "Computes the hyperbolic tangent, \
         rounding to the nearest.",
        tanh,
        "Computes the hyperboic tangent, \
         applying the specified rounding method.",
        tanh_round,
        mpc::mpc_tanh
    }
    math_op1! {
        "Computes the inverse sine, \
         rounding to the nearest.",
        asin,
        "Computes the inverse sine, \
         applying the specified rounding method.",
        asin_round,
        mpc::mpc_asin
    }
    math_op1! {
        "Computes the inverse cosine, \
         rounding to the nearest.",
        acos,
        "Computes the inverse cosine, \
         applying the specified rounding method.",
        acos_round,
        mpc::mpc_acos
    }
    math_op1! {
        "Computes the inverse tangent, \
         rounding to the nearest.",
        atan,
        "Computes the inverse tangent, \
         applying the specified rounding method.",
        atan_round,
        mpc::mpc_atan
    }
    math_op1! {
        "Computes the inverse hyperbolic sine, \
         rounding to the nearest.",
        asinh,
        "Computes the inverse hyperboic sine, \
         applying the specified rounding method.",
        asinh_round,
        mpc::mpc_asinh
    }
    math_op1! {
        "Computes the inverse hyperbolic cosine, \
         rounding to the nearest.",
        acosh,
        "Computes the inverse hyperboic cosine, \
         applying the specified rounding method.",
        acosh_round,
        mpc::mpc_acosh
    }
    math_op1! {
        "Computes the inverse hyperbolic tangent, \
         rounding to the nearest.",
        atanh,
        "Computes the inverse hyperboic tangent, \
         applying the specified rounding method.",
        atanh_round,
        mpc::mpc_atanh
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_bits_round).
    pub fn assign_random_bits<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_bits_round(rng, (Round::Nearest, Round::Nearest));
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, round.0)`]
    /// (../rugflo/struct.Float.html#method.assign_random_bits_round)
    /// on the real part, and the same with `round.1` on the
    /// imaginary part.
    pub fn assign_random_bits_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round2)
                                            -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_bits_round(rng, round.0),
         imag.assign_random_bits_round(rng, round.1))
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number, rounding to the nearest.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_cont_round).
    pub fn assign_random_cont<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_cont_round(rng, (Round::Nearest, Round::Nearest));
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number, applying the specified
    /// rounding method.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, round.0)`]
    /// (../rugflo/struct.Float.html#method.assign_random_bits_round)
    /// on the real part, and the same with `round.1` on the
    /// imaginary part.
    pub fn assign_random_cont_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round2)
                                            -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_cont_round(rng, round.0),
         imag.assign_random_cont_round(rng, round.1))
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` rounding to the nearest.
    /// The exponent is encoded in decimal.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self, radix: i32) -> String {
        self.make_string(radix, (Round::Nearest, Round::Nearest))
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` applying the specified rounding method.
    /// The exponent is encoded in decimal.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix_round(&self, radix: i32, round: Round2) -> String {
        self.make_string(radix, round)
    }

    /// Parses a `Complex` number with the specified precision,
    /// rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    pub fn from_str(src: &str, prec: Prec2) -> Result<Complex, ()> {
        let mut val = Complex::new(prec);
        val.assign_str(src)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str,
                          radix: i32,
                          prec: Prec2)
                          -> Result<Complex, ()> {
        let mut val = Complex::new(prec);
        val.assign_str_radix(src, radix)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified precision,
    /// applying the specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_round).
    pub fn from_str_round(src: &str,
                          prec: Prec2,
                          round: Round2)
                          -> Result<(Complex, Ordering2), ()> {
        let mut val = Complex::new(prec);
        let ord = val.assign_str_round(src, round)?;
        Ok((val, ord))
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, applying the specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix_round).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix_round(src: &str,
                                radix: i32,
                                prec: Prec2,
                                round: Round2)
                                -> Result<(Complex, Ordering2), ()> {
        let mut val = Complex::new(prec);
        let ord = val.assign_str_radix_round(src, radix, round)?;
        Ok((val, ord))
    }

    /// Parses a `Complex` number from a string, rounding to the
    /// nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    /// let mut c = Complex::new((53, 53));
    /// c.assign_str("(12.5e2 2.5e-1)").unwrap();
    /// assert!(*c.real() == 12.5e2);
    /// assert!(*c.imag() == 2.5e-1);
    /// let ret = c.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ()> {
        self.assign_str_round(src, (Round::Nearest, Round::Nearest))?;
        Ok(())
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    /// let mut c = Complex::new((53, 53));
    /// c.assign_str_radix("f.f", 16).unwrap();
    /// assert!(*c.real() == 15.9375);
    /// assert!(*c.imag() == 0);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ()> {
        self.assign_str_radix_round(src,
                                    radix,
                                    (Round::Nearest, Round::Nearest))?;
        Ok(())
    }

    /// Parses a `Complex` number from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugflo::Round;
    /// use rugcom::Complex;
    /// use std::cmp::Ordering;
    ///
    /// fn main() {
    ///     let mut c = Complex::new((4, 4));
    ///     let round = (Round::Down, Round::Up);
    ///     let dir = c.assign_str_round("(14.1 14.2)", round).unwrap();
    ///     assert!(*c.real() == 14);
    ///     assert!(*c.imag() == 15);
    ///     assert!(dir == (Ordering::Less, Ordering::Greater));
    /// }
    /// ```
    pub fn assign_str_round(&mut self,
                            src: &str,
                            round: Round2)
                            -> Result<Ordering2, ()> {
        let c_str = CString::new(src).map_err(|_| ())?;
        let ord = unsafe {
            mpc::mpc_set_str(raw_mut(self), c_str.as_ptr(), 0, rraw2(round))
        };
        if ord < 0 {
            self.assign(0);
            Err(())
        } else {
            Ok(ordering2(ord))
        }
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugflo::Round;
    /// use rugcom::Complex;
    /// use std::cmp::Ordering;
    ///
    /// fn main() {
    ///     let mut c = Complex::new((4, 4));
    ///     let round = (Round::Nearest, Round::Nearest);
    ///     let dir = c.assign_str_radix_round("(c.c c.1)", 16, round).unwrap();
    ///     assert!(*c.real() == 13);
    ///     assert!(*c.imag() == 12);
    ///     assert!(dir == (Ordering::Greater, Ordering::Less));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix_round(&mut self,
                                  src: &str,
                                  radix: i32,
                                  round: Round2)
                                  -> Result<Ordering2, ()> {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let c_str = CString::new(src).map_err(|_| ())?;
        let ord = unsafe {
            mpc::mpc_set_str(raw_mut(self), c_str.as_ptr(), radix, rraw2(round))
        };
        if ord < 0 {
            self.assign(0);
            Err(())
        } else {
            Ok(ordering2(ord))
        }
    }
}

impl<T> From<(T, (i32, i32))> for Complex
    where Complex: From<(T, (u32, u32))>
{
    fn from((t, prec): (T, (i32, i32))) -> Complex {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from((t, (prec.0 as u32, prec.1 as u32)))
    }
}

impl<T> FromRound<T, (i32, i32)> for Complex
    where Complex: FromRound<T,
                             (u32, u32),
                             Round = Round2,
                             Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T,
                  prec: (i32, i32),
                  round: Round2)
                  -> (Complex, Ordering2) {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from_round(t, (prec.0 as u32, prec.1 as u32), round)
    }
}

macro_rules! from_life_a {
    { $d:expr, $t:ty } => {
        impl<'a> From<($t, Prec2)> for Complex {
            /// Constructs a `Complex` number from
            #[doc=$d]
            /// with the specified precisions, rounding to the nearest.
            fn from((t, prec): ($t, Prec2)) -> Complex {
                let mut ret = Complex::new(prec);
                ret.assign(t);
                ret
            }
        }

        impl<'a> FromRound<$t, Prec2> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Constructs a `Complex` number from
            #[doc=$d]
            /// with the specified precisions, applying the specified
            /// rounding method.
            fn from_round(t: $t, prec: Prec2, round: Round2)
                          -> (Complex, Ordering2) {
                let mut ret = Complex::new(prec);
                let ord = ret.assign_round(t, round);
                (ret, ord)
            }
        }
    };
}

macro_rules! from {
    { $d:expr, $t:ty } => {
        impl From<($t, Prec2)> for Complex {
            /// Constructs a `Complex` number from
            #[doc=$d]
            /// with the specified precisions, rounding to the nearest.
            fn from((t, prec): ($t, Prec2)) -> Complex {
                Complex::from_round(t, prec, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl FromRound<$t, Prec2> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Constructs a `Complex` number from
            #[doc=$d]
            /// with the specified precisions, applying the specified
            /// rounding method.
            fn from_round(t: $t, prec: Prec2, round: Round2)
                          -> (Complex, Ordering2) {
                let mut ret = Complex::new(prec);
                let ord = ret.assign_round(t, round);
                (ret, ord)
            }
        }
    };
}

from! { "an `Integer`", Integer }
from! { "a `Rational` number", Rational }
from! { "a `Float`", Float }
from! { "another `Complex` number", Complex }
from_life_a! { "an `Integer`", &'a Integer }
from_life_a! { "a `Rational` number", &'a Rational }
from_life_a! { "a `Float`", &'a Float }
from_life_a! { "another `Complex` number", &'a Complex }
from! { "a `u32`", u32 }
from! { "an `i32`", i32 }
from! { "an `f64`", f64 }
from! { "an `f32`", f32 }

from! { "a real and an imaginary `Integer`", (Integer, Integer) }
from! { "a real and an imaginary `Rational` number", (Rational, Rational) }
from! { "a real and an imaginary `Float`", (Float, Float) }
from_life_a! { "a real and an imaginary `Integer`", (&'a Integer, &'a Integer) }
from_life_a! { "a real and an imaginary `Rational` number",
                (&'a Rational, &'a Rational) }
from_life_a! { "a real and an imaginary `Float`", (&'a Float, &'a Float) }
from! { "a real and an imaginary `u32`", (u32, u32) }
from! { "a real and an imaginary `i32`", (i32, i32) }
from! { "a real and an imaginary `f64`", (f64, f64) }
from! { "a real and an imaginary `f32`", (f32, f32) }

macro_rules! assign {
    { $d:expr, $t:ty, $reft:ty, $addr:expr, $eval:expr } => {
        impl<'a> Assign<$reft> for Complex {
            /// Assigns from
            #[doc=$d]
            /// and rounds to the nearest.
            fn assign(&mut self, other: $reft) {
                self.assign_round(other, (Round::Nearest, Round::Nearest));
            }
        }

        impl<'a> AssignRound<$reft> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Assigns from
            #[doc=$d]
            /// and applies the specified rounding method.
            fn assign_round(&mut self, other: $reft, round: Round2)
                            -> Ordering2 {
                let ord = $eval(raw_mut(self), other, rraw2(round));
                ordering2(ord)
            }
        }

        impl Assign<$t> for Complex {
            /// Assigns from
            #[doc=$d]
            /// and rounds to the nearest.
            fn assign(&mut self, other: $t) {
                self.assign_round($addr(&other),
                                  (Round::Nearest, Round::Nearest));
            }
        }

        impl AssignRound<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Assigns from
            #[doc=$d]
            /// and applies the specified rounding method.
            fn assign_round(&mut self, other: $t, round: Round2) -> Ordering2 {
                self.assign_round($addr(&other), round)
            }
        }
    };
}

fn unit<T>(val: T) -> T {
    val
}
fn tup_ref<T>(pair: &(T, T)) -> (&T, &T) {
    (&pair.0, &pair.1)
}

assign! { "an `Integer`", Integer, &'a Integer, unit,
           |c, t, r| unsafe { mpc::mpc_set_z(c, integer_raw(t), r) } }
assign! { "a `Rational` number", Rational, &'a Rational, unit,
           |c, t, r| unsafe { mpc::mpc_set_q(c, rational_raw(t), r) } }
assign! { "a `Float`", Float, &'a Float, unit,
           |c, t, r| unsafe { mpc::mpc_set_fr(c, float_raw(t), r) } }
assign! { "another `Complex` number", Complex, &'a Complex, unit,
           |c, t, r| unsafe { mpc::mpc_set(c, raw(t), r) } }

assign! { "a real and an imaginary `Integer`",
           (Integer, Integer), (&'a Integer, &'a Integer), tup_ref,
           |c, t: (&Integer, &Integer), r| unsafe {
               mpc::mpc_set_z_z(c, integer_raw(t.0), integer_raw(t.1), r) } }
assign! { "a real and an imaginary `Rational` number",
           (Rational, Rational), (&'a Rational, &'a Rational), tup_ref,
           |c, t: (&Rational, &Rational), r| unsafe {
               mpc::mpc_set_q_q(c, rational_raw(t.0), rational_raw(t.1), r) }}
assign! { "a real and an imaginary `Float`",
           (Float, Float), (&'a Float, &'a Float), tup_ref,
           |c, t: (&Float, &Float), r| unsafe {
               mpc::mpc_set_fr_fr(c, float_raw(t.0), float_raw(t.1), r) } }

macro_rules! assign_prim {
    { $d:expr, $d_pair:expr, $t:ty, $func:path, $func_pair:path } => {
        impl Assign<$t> for Complex {
            /// Assigns from
            #[doc=$d]
            /// and rounds to the nearest.
            fn assign(&mut self, other: $t) {
                self.assign_round(other, (Round::Nearest, Round::Nearest));
            }
        }

        impl AssignRound<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Assigns from
            #[doc=$d]
            /// and applies the specified rounding method.
            fn assign_round(&mut self, other: $t, round: Round2) -> Ordering2 {
                ordering2(unsafe {
                    $func(raw_mut(self), other.into(), rraw2(round))
                })
            }
        }
        impl Assign<($t, $t)> for Complex {
            /// Assigns from
            #[doc=$d_pair]
            /// and rounds to the nearest.
            fn assign(&mut self, other: ($t, $t)) {
                self.assign_round(other, (Round::Nearest, Round::Nearest));
            }
        }

        impl AssignRound<($t, $t)> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            /// Assigns from
            #[doc=$d_pair]
            /// and applies the specified rounding method.
            fn assign_round(&mut self,
                            other: ($t, $t),
                            round: Round2)
                            -> Ordering2 {
                ordering2(unsafe {
                    $func_pair(raw_mut(self),
                               other.0.into(),
                               other.1.into(),
                               rraw2(round))
                })
            }
        }
    };
}

assign_prim! { "a `u32`", "a real and an imaginary `u32`", u32,
                mpc::mpc_set_ui, mpc::mpc_set_ui_ui }
assign_prim! { "an `i32`", "a real and an imaginary `i32`", i32,
                mpc::mpc_set_si, mpc::mpc_set_si_si }
assign_prim! { "an `f32`", "a real and an imaginary `f32`", f32,
                mpc::mpc_set_d, mpc::mpc_set_d_d }
assign_prim! { "an `f64`", "a real and an imaginary `f64`", f64,
                mpc::mpc_set_d, mpc::mpc_set_d_d }

macro_rules! arith_for_complex {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $eval:expr) => {
        impl<'a> $imp<&'a $t> for Complex {
            type Output = Complex;
            fn $method(self, op: &'a $t) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp<$t> for Complex {
            type Output = Complex;
            fn $method(self, op: $t) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl<'a> $imp_round<&'a $t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(mut self, op: &'a $t, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = $eval(raw_mut(&mut self),
                                op,
                                rraw2(round));
                (self, ordering2(ord))
            }
        }

        impl $imp_round<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: $t, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(&op, round)
            }
        }

        impl<'a> $imp_assign<&'a $t> for Complex {
            fn $method_assign(&mut self, op: &'a $t) {
                $eval(raw_mut(self),
                      op,
                      rraw2((Round::Nearest, Round::Nearest)));
            }
        }

        impl $imp_assign<$t> for Complex {
            fn $method_assign(&mut self, op: $t) {
                self.$method_assign(&op);
            }
        }
    };
}

macro_rules! arith_commut {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $eval:expr) => {
        arith_for_complex! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $eval
        }

        impl $imp<Complex> for $t {
            type Output = Complex;
            fn $method(self, op: Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl<'a> $imp<&'a Complex> for $t {
            type Output = Complex;
            fn $method(self, op: &'a Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                op.$method_round(self, round)
            }
        }

        impl<'a> $imp_round<&'a Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: &'a Complex, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(op.clone(), round)
            }
        }
    };
}

macro_rules! arith_non_commut {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $imp_from_assign:ident $method_from_assign:ident,
     $t:ty,
     $eval:expr,
     $eval_from:expr) => {
        arith_for_complex! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $eval
        }

        impl $imp<Complex> for $t {
            type Output = Complex;
            fn $method(self, op: Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl<'a> $imp<&'a Complex> for $t {
            type Output = Complex;
            fn $method(self, op: &'a Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, mut op: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = $eval_from(&self, raw_mut(&mut op), rraw2(round));
                (op, ordering2(ord))
            }
        }

        impl<'a> $imp_round<&'a Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: &'a Complex, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(op.clone(), round)
            }
        }

        impl $imp_from_assign<$t> for Complex {
            fn $method_from_assign(&mut self, lhs: $t) {
                self.$method_from_assign(&lhs);
            }
        }

        impl<'a> $imp_from_assign<&'a $t> for Complex {
            fn $method_from_assign(&mut self, lhs: &$t) {
                let round = (Round::Nearest, Round::Nearest);
                $eval_from(lhs, raw_mut(self), rraw2(round));
            }
        }
    };
}

arith_for_complex! { Add add, AddRound add_round, AddAssign add_assign, Complex,
                     |c, t, r| unsafe { mpc::mpc_add(c, c, raw(t), r) } }
arith_for_complex! { Sub sub, SubRound sub_round, SubAssign sub_assign, Complex,
                     |c, t, r| unsafe { mpc::mpc_sub(c, c, raw(t), r) } }

impl SubFromAssign for Complex {
    fn sub_from_assign(&mut self, lhs: Complex) {
        self.sub_from_assign(&lhs);
    }
}

impl<'a> SubFromAssign<&'a Complex> for Complex {
    fn sub_from_assign(&mut self, lhs: &Complex) {
        unsafe {
            mpc::mpc_sub(raw_mut(self),
                         raw(lhs),
                         raw(self),
                         rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

arith_for_complex! { Mul mul, MulRound mul_round, MulAssign mul_assign, Complex,
                     |c, t, r| unsafe { mpc::mpc_mul(c, c, raw(t), r) } }
arith_for_complex! { Div div, DivRound div_round, DivAssign div_assign, Complex,
                     |c, t, r| unsafe { mpc::mpc_div(c, c, raw(t), r) } }

impl DivFromAssign for Complex {
    fn div_from_assign(&mut self, lhs: Complex) {
        self.div_from_assign(&lhs);
    }
}

impl<'a> DivFromAssign<&'a Complex> for Complex {
    fn div_from_assign(&mut self, lhs: &Complex) {
        unsafe {
            mpc::mpc_div(raw_mut(self),
                         raw(lhs),
                         raw(self),
                         rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

arith_commut! { Add add, AddRound add_round, AddAssign add_assign, Float,
                |c, t, r| unsafe { mpc::mpc_add_fr(c, c, float_raw(t), r) } }

arith_non_commut! { Sub sub, SubRound sub_round, SubAssign sub_assign,
                    SubFromAssign sub_from_assign, Float,
                   |c, t, r| unsafe { mpc::mpc_sub_fr(c, c, float_raw(t), r) },
                   |t, c, r| unsafe { mpc::mpc_fr_sub(c, float_raw(t), c, r) }}

arith_commut! { Mul mul, MulRound mul_round, MulAssign mul_assign, Float,
                |c, t, r| unsafe { mpc::mpc_mul_fr(c, c, float_raw(t), r) } }
arith_non_commut! { Div div, DivRound div_round, DivAssign div_assign,
                    DivFromAssign div_from_assign, Float,
                   |c, t, r| unsafe { mpc::mpc_div_fr(c, c, float_raw(t), r) },
                   |t, c, r| unsafe { mpc::mpc_fr_div(c, float_raw(t), c, r) }}

macro_rules! arith_prim_for_complex {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $func:path) => {
        impl $imp<$t> for Complex {
            type Output = Complex;
            fn $method(self, op: $t) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(mut self, op: $t, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = unsafe {
                    $func(raw_mut(&mut self),
                          raw(&self),
                          op.into(),
                          rraw2(round))
                };
                (self, ordering2(ord))
            }
        }

        impl $imp_assign<$t> for Complex {
            fn $method_assign(&mut self, op: $t) {
                unsafe {
                    $func(raw_mut(self),
                          raw(self),
                          op.into(),
                          rraw2((Round::Nearest, Round::Nearest)));
                }
            }
        }
    };
}

macro_rules! arith_prim_non_commut {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $imp_from_assign:ident $method_from_assign:ident,
     $t:ty,
     $func:path,
     $func_from:path) => {
        arith_prim_for_complex! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Complex> for $t {
            type Output = Complex;
            fn $method(self, op: Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl<'a> $imp<&'a Complex> for $t {
            type Output = Complex;
            fn $method(self, op: &'a Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, mut op: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = unsafe {
                    $func_from(raw_mut(&mut op),
                               self.into(),
                               raw(&op),
                               rraw2(round))
                };
                (op, ordering2(ord))
            }
        }

        impl<'a> $imp_round<&'a Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: &'a Complex, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(op.clone(), round)
            }
        }

        impl $imp_from_assign<$t> for Complex {
            fn $method_from_assign(&mut self, lhs: $t) {
                unsafe {
                    $func_from(raw_mut(self),
                               lhs.into(),
                               raw(self),
                               rraw2((Round::Nearest, Round::Nearest)));
                }
            }
        }
    };
}

macro_rules! arith_prim_commut {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $func:path) => {
        arith_prim_for_complex! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Complex> for $t {
            type Output = Complex;
            fn $method(self, op: Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl<'a> $imp<&'a Complex> for $t {
            type Output = Complex;
            fn $method(self, op: &'a Complex) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                op.$method_round(self, round)
            }
        }

        impl<'a> $imp_round<&'a Complex> for $t {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, op: &'a Complex, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(op.clone(), round)
            }
        }
    };
}

arith_prim_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    u32,
    mpc::mpc_add_ui
}
arith_prim_non_commut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    u32,
    mpc::mpc_sub_ui,
    ui_sub
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    u32,
    mpc::mpc_mul_ui
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    i32,
    mpc::mpc_mul_si
}
arith_prim_non_commut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    u32,
    mpc::mpc_div_ui,
    mpc::mpc_ui_div
}

unsafe fn ui_sub(x: *mut mpc::mpc_t,
                 y: c_ulong,
                 z: *const mpc::mpc_t,
                 r: mpc::mpc_rnd_t)
                 -> c_int {
    mpc::mpc_ui_ui_sub(x, y, 0, z, r)
}

impl Sub<Complex> for (u32, u32) {
    type Output = Complex;
    fn sub(self, op: Complex) -> Complex {
        self.sub_round(op, (Round::Nearest, Round::Nearest)).0
    }
}

impl<'a> Sub<&'a Complex> for (u32, u32) {
    type Output = Complex;
    fn sub(self, op: &'a Complex) -> Complex {
        self.sub_round(op, (Round::Nearest, Round::Nearest)).0
    }
}

impl SubRound<Complex> for (u32, u32) {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    fn sub_round(self, mut op: Complex, round: Round2) -> (Complex, Ordering2) {
        let ord = unsafe {
            mpc::mpc_ui_ui_sub(raw_mut(&mut op),
                               self.0.into(),
                               self.1.into(),
                               raw(&op),
                               rraw2(round))
        };
        (op, ordering2(ord))
    }
}

impl<'a> SubRound<&'a Complex> for (u32, u32) {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    fn sub_round(self, op: &'a Complex, round: Round2) -> (Complex, Ordering2) {
        self.sub_round(op.clone(), round)
    }
}

impl SubFromAssign<(u32, u32)> for Complex {
    fn sub_from_assign(&mut self, lhs: (u32, u32)) {
        unsafe {
            mpc::mpc_ui_ui_sub(raw_mut(self),
                               lhs.0.into(),
                               lhs.1.into(),
                               raw(self),
                               rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

impl Neg for Complex {
    type Output = Complex;
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    fn neg_assign(&mut self) {
        let round = (Round::Nearest, Round::Nearest);
        unsafe {
            mpc::mpc_neg(raw_mut(self), raw(self), rraw2(round));
        }
    }
}

macro_rules! sh_op {
    { $doc:expr,
      $imp:ident $method:ident,
      $imp_round:ident $method_round:ident,
      $imp_assign:ident $method_assign:ident,
      $t:ty,
      $func:path } => {
        impl $imp<$t> for Complex {
            type Output = Complex;
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, rounding to the
            /// nearest.
            fn $method(self, op: $t) -> Complex {
                self.$method_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl $imp_round<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, applying the
            /// specified rounding.
            fn $method_round(mut self, op: $t, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = unsafe {
                    $func(raw_mut(&mut self),
                          raw(&self),
                          op.into(),
                          rraw2(round))
                };
                (self, ordering2(ord))
            }
        }

        impl $imp_assign<$t> for Complex {
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, rounding to the
            /// nearest.
            fn $method_assign(&mut self, op: $t) {
                unsafe {
                    $func(raw_mut(self),
                          raw(self),
                          op.into(),
                          rraw2((Round::Nearest, Round::Nearest)));
                }
            }
        }
    }
}

sh_op! {
    "Multiplies",
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    u32,
    mpc::mpc_mul_2ui
}
sh_op! {
    "Divides",
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    u32,
    mpc::mpc_div_2ui
}
sh_op! {
    "Multiplies",
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    i32,
    mpc::mpc_mul_2si
}
sh_op! {
    "Divides",
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    i32,
    mpc::mpc_div_2si
}

macro_rules! pow_others {
    { $($t:ty)* } => { $(
        impl<'a> Pow<&'a $t> for Complex {
            type Output = Complex;
            fn pow(self, op: &'a $t) -> Complex {
                self.pow_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl Pow<$t> for Complex {
            type Output = Complex;
            fn pow(self, op: $t) -> Complex {
                self.pow_round(op, (Round::Nearest, Round::Nearest)).0
            }
        }

        impl PowRound<$t> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn pow_round(self, op: $t, round: Round2) -> (Complex, Ordering2) {
                self.pow_round(&op, round)
            }
        }

        impl PowAssign<$t> for Complex {
            fn pow_assign(&mut self, op: $t) {
                self.pow_assign(&op);
            }
        }
    )* };
}

impl<'a> PowRound<&'a Integer> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    fn pow_round(mut self,
                 op: &'a Integer,
                 round: Round2)
                 -> (Complex, Ordering2) {
        let ord = unsafe {
            mpc::mpc_pow_z(raw_mut(&mut self),
                           raw(&self),
                           integer_raw(op),
                           rraw2(round))
        };
        (self, ordering2(ord))
    }
}

impl<'a> PowAssign<&'a Integer> for Complex {
    fn pow_assign(&mut self, op: &'a Integer) {
        unsafe {
            mpc::mpc_pow_z(raw_mut(self),
                           raw(self),
                           integer_raw(op),
                           rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

impl<'a> PowRound<&'a Float> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    fn pow_round(mut self,
                 op: &'a Float,
                 round: Round2)
                 -> (Complex, Ordering2) {
        let ord = unsafe {
            mpc::mpc_pow_fr(raw_mut(&mut self),
                            raw(&self),
                            float_raw(op),
                            rraw2(round))
        };
        (self, ordering2(ord))
    }
}

impl<'a> PowAssign<&'a Float> for Complex {
    fn pow_assign(&mut self, op: &'a Float) {
        unsafe {
            mpc::mpc_pow_fr(raw_mut(self),
                            raw(self),
                            float_raw(op),
                            rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

impl<'a> PowRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    fn pow_round(mut self,
                 op: &'a Complex,
                 round: Round2)
                 -> (Complex, Ordering2) {
        let ord = unsafe {
            mpc::mpc_pow(raw_mut(&mut self), raw(&self), raw(op), rraw2(round))
        };
        (self, ordering2(ord))
    }
}

impl<'a> PowAssign<&'a Complex> for Complex {
    fn pow_assign(&mut self, op: &'a Complex) {
        unsafe {
            mpc::mpc_pow(raw_mut(self),
                         raw(self),
                         raw(op),
                         rraw2((Round::Nearest, Round::Nearest)));
        }
    }
}

pow_others! { Integer Float Complex }

impl Complex {
    fn make_string(&self, radix: i32, round: Round2) -> String {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let mut buf = String::new();
        let s;
        let cstr;
        unsafe {
            s = mpc::mpc_get_str(radix.into(), 0, raw(self), rraw2(round));
            assert!(!s.is_null());
            cstr = CStr::from_ptr(s);
            buf.push_str(cstr.to_str().unwrap());
            mpc::mpc_free_str(s);
        }
        buf
    }
}

impl fmt::Display for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string_radix(10))
    }
}
impl fmt::Debug for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let round = (Round::Nearest, Round::Nearest);
        write!(f, "{}", self.make_string(16, round))
    }
}

impl fmt::Binary for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let round = (Round::Nearest, Round::Nearest);
        write!(f, "{}", self.make_string(2, round))
    }
}

impl fmt::Octal for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let round = (Round::Nearest, Round::Nearest);
        write!(f, "{}", self.make_string(8, round))
    }
}

impl fmt::LowerHex for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let round = (Round::Nearest, Round::Nearest);
        write!(f, "{}", self.make_string(16, round))
    }
}

impl fmt::UpperHex for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let round = (Round::Nearest, Round::Nearest);
        write!(f, "{}", self.make_string(16, round))
    }
}

fn integer_raw(z: &Integer) -> &gmp::mpz_t {
    let ptr = z as *const _ as *const gmp::mpz_t;
    unsafe { &*ptr }
}

fn rational_raw(q: &Rational) -> &gmp::mpq_t {
    let ptr = q as *const _ as *const gmp::mpq_t;
    unsafe { &*ptr }
}

fn float_raw(f: &Float) -> &mpfr::mpfr_t {
    let ptr = f as *const _ as *const mpfr::mpfr_t;
    unsafe { &*ptr }
}

fn float_raw_mut(f: &mut Float) -> &mut mpfr::mpfr_t {
    let ptr = f as *mut _ as *mut mpfr::mpfr_t;
    unsafe { &mut *ptr }
}

fn rraw(round: Round) -> mpfr::mpfr_rnd_t {
    match round {
        Round::Nearest => mpfr::mpfr_rnd_t::MPFR_RNDN,
        Round::Zero => mpfr::mpfr_rnd_t::MPFR_RNDZ,
        Round::Up => mpfr::mpfr_rnd_t::MPFR_RNDU,
        Round::Down => mpfr::mpfr_rnd_t::MPFR_RNDD,
        Round::AwayFromZero => mpfr::mpfr_rnd_t::MPFR_RNDA,
    }
}

fn rraw2(round: Round2) -> mpc::mpc_rnd_t {
    if round.0 == Round::AwayFromZero || round.1 == Round::AwayFromZero {
        unimplemented!();
    }
    (rraw(round.0) as mpc::mpc_rnd_t) + ((rraw(round.1) as mpc::mpc_rnd_t) << 4)
}

fn ordering2(ord: i32) -> (Ordering, Ordering) {
    // ord == first + 4 * second
    let first = match ord % 4 {
        0 => Ordering::Equal,
        1 => Ordering::Greater,
        2 => Ordering::Less,
        _ => unreachable!(),
    };
    let second = match ord / 4 {
        0 => Ordering::Equal,
        1 => Ordering::Greater,
        2 => Ordering::Less,
        _ => unreachable!(),
    };
    (first, second)
}
