// Copyright © 2016–2017 University of Malta

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

use {AddRound, AssignRound, DivRound, FromRound, MulRound, PowRound, ShlRound,
     ShrRound, SubRound};
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
#[cfg(feature = "random")]
use rand::Rng;
use rugint::{Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign,
             SubFromAssign};
use rugrat::Rational;
use std::{i32, u32};
use std::ascii::AsciiExt;
use std::cmp::{self, Ordering};
use std::error::Error;
use std::ffi::{CStr, CString};
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
#[cfg(feature = "random")]
use std::os::raw::c_uint;
use std::ptr;
#[cfg(feature = "random")]
use std::slice;

/// Returns the minimum value for the exponent.
pub fn exp_min() -> i32 {
    let min = unsafe { mpfr::get_emin() };
    if mem::size_of::<mpfr::exp_t>() <= mem::size_of::<i32>() ||
       min > i32::MIN as mpfr::exp_t {
        min as i32
    } else {
        i32::MIN
    }
}

/// Returns the maximum value for the exponent.
pub fn exp_max() -> i32 {
    let max = unsafe { mpfr::get_emax() };
    if mem::size_of::<mpfr::exp_t>() <= mem::size_of::<i32>() ||
       max < i32::MAX as mpfr::exp_t {
        max as i32
    } else {
        i32::MAX
    }
}

/// Returns the minimum value for the precision.
pub fn prec_min() -> u32 {
    mpfr::PREC_MIN as u32
}

/// Returns the maximum value for the precision.
pub fn prec_max() -> u32 {
    let max = mpfr::PREC_MAX;
    if mem::size_of::<mpfr::prec_t>() <= mem::size_of::<u32>() ||
       max < u32::MAX as mpfr::prec_t {
        max as u32
    } else {
        u32::MAX
    }
}

/// The rounding methods for floating-point values.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Round {
    /// Round towards the nearest.
    ///
    /// When the number to be rounded is exactly between two
    /// representable numbers, it is rounded to the even one, that is,
    /// the one with the least significant bit set to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::{AssignRound, Float, Round};
    /// // 24 is 11000 in binary
    /// // 25 is 11001 in binary
    /// // 26 is 11010 in binary
    /// // 27 is 11011 in binary
    /// // 28 is 11100 in binary
    /// let mut f4 = Float::new(4);
    /// f4.assign_round(25, Round::Nearest);
    /// assert!(f4 == 24);
    /// f4.assign_round(27, Round::Nearest);
    /// assert!(f4 == 28);
    /// ```
    Nearest,
    /// Round towards zero.
    Zero,
    /// Round towards plus infinity.
    Up,
    /// Round towards minus infinity.
    Down,
    /// Round away from zero.
    AwayFromZero,
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

/// The available floating-point constants.
///
/// # Examples
///
/// ```rust
/// use rugflo::{Constant, Float};
///
/// let log2 = Float::from((Constant::Log2, 53));
/// let pi = Float::from((Constant::Pi, 53));
/// let euler = Float::from((Constant::Euler, 53));
/// let catalan = Float::from((Constant::Catalan, 53));
///
/// assert!(log2.to_string_radix(10, Some(5)) == "6.9315e-1");
/// assert!(pi.to_string_radix(10, Some(5)) == "3.1416e0");
/// assert!(euler.to_string_radix(10, Some(5)) == "5.7722e-1");
/// assert!(catalan.to_string_radix(10, Some(5)) == "9.1597e-1");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Constant {
    /// The logarithm of two, 0.693...
    Log2,
    /// The value of pi, 3.141...
    Pi,
    /// Euler's constant, 0.577...
    Euler,
    /// Catalan's constant, 0.915...
    Catalan,
}

/// Special floating-point values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Special {
    /// Positive zero.
    Zero,
    /// Negative zero.
    MinusZero,
    /// Positive infinity.
    Infinity,
    /// Negative infinity.
    MinusInfinity,
    /// Not a number.
    Nan,
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

/// A multi-precision floating-point number.
/// The precision has to be set during construction.
///
/// There are two versions of most methods:
///
/// 1. The first rounds the returned or stored `Float` to the
///    [nearest](enum.Round.html#variant.Nearest) representable value.
/// 2. The second applies the specified [rounding
///    method](enum.Round.html), and returns the rounding direction:
///    * `Ordering::Less` if the returned/stored `Float` is less than
///      the exact result,
///    * `Ordering::Equal` if the returned/stored `Float` is equal to
///      the exact result,
///    * `Ordering::Greater` if the returned/stored `Float` is greater
///      than the exact result,
pub struct Float {
    inner: mpfr_t,
}

impl Drop for Float {
    fn drop(&mut self) {
        unsafe {
            mpfr::clear(&mut self.inner);
        }
    }
}

impl Clone for Float {
    fn clone(&self) -> Float {
        let mut ret = Float::new(self.prec());
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Float) {
        self.set_prec(source.prec());
        self.assign(source);
    }
}

macro_rules! math_op1 {
    { $d:expr,
      $method:ident,
      $d_round:expr,
      $method_round:ident,
      $func:path $(, $param:ident: $t:ty)* } => {
        #[doc=$d]
        pub fn $method(&mut self $(, $param: $t)*) -> &mut Float {
            self.$method_round($($param,)* Round::Nearest);
            self
        }

        #[doc=$d_round]
        pub fn $method_round(&mut self, $($param: $t,)* round: Round)
                             -> Ordering {
            unsafe {
                $func(&mut self.inner,
                      &self.inner,
                      $($param.into(),)*
                      rraw(round))
                    .cmp(&0)
            }
        }
    };
}

macro_rules! math_op2 {
    { $d:expr,
      $method:ident,
      $d_round:expr,
      $method_round:ident,
      $func:path } => {
        #[doc=$d]
        pub fn $method(&mut self, other: &Float) -> &mut Float {
            self.$method_round(other, Round::Nearest);
            self
        }

        #[doc=$d_round]
        pub fn $method_round(&mut self, other: &Float, round: Round)
                             -> Ordering {
            unsafe {
                $func(&mut self.inner, &self.inner, &other.inner, rraw(round))
                    .cmp(&0)
            }
        }
    };
}

impl Float {
    /// Create a new floating-point number with the specified
    /// precision and with value 0.
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    pub fn new(prec: u32) -> Float {
        assert!(prec >= prec_min() && prec <= prec_max(),
                "precision out of range");
        unsafe {
            let mut inner: mpfr_t = mem::uninitialized();
            mpfr::init2(&mut inner, prec as mpfr::prec_t);
            mpfr::set_zero(&mut inner, 0);
            Float { inner: inner }
        }
    }

    /// Returns the precision of `self`.
    pub fn prec(&self) -> u32 {
        unsafe { mpfr::get_prec(&self.inner) as u32 }
    }

    /// Sets the precision of `self` exactly, rounding to the nearest.
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    pub fn set_prec(&mut self, prec: u32) {
        self.set_prec_round(prec, Round::Nearest);
    }

    /// Sets the precision of `self` exactly, applying the specified
    /// rounding method.
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    pub fn set_prec_round(&mut self, prec: u32, round: Round) -> Ordering {
        assert!(prec >= prec_min() && prec <= prec_max(),
                "precision out of range");
        unsafe {
            mpfr::prec_round(&mut self.inner, prec as mpfr::prec_t, rraw(round))
                .cmp(&0)
        }
    }

    /// Converts to an integer, rounding to the nearest.
    pub fn to_integer(&self) -> Integer {
        self.to_integer_round(Round::Nearest).0
    }

    /// Converts to an integer, applying the specified rounding method.
    pub fn to_integer_round(&self, round: Round) -> (Integer, Ordering) {
        let mut i = Integer::new();
        let ord = unsafe {
            mpfr::get_z(integer_inner_mut(&mut i), &self.inner, rraw(round))
                .cmp(&0)
        };
        (i, ord)
    }

    /// If `self` is a [finite number](#method.is_number), returns an
    /// integer and exponent such that `self` is exactly equal to the
    /// integer multiplied by two raised to the power of the exponent.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugflo;
    /// use rugint::Assign;
    /// use rugflo::{Float, Special};
    ///
    /// fn main() {
    ///     let mut float = Float::from((6.5, 16));
    ///     // 6.5 in binary is 110.1
    ///     // Since the precision is 16 bits, this becomes
    ///     // 1101_0000_0000_0000 times two to the power of -12
    ///     let (int, exp) = float.to_integer_exp().unwrap();
    ///     assert!(int == 0b1101_0000_0000_0000);
    ///     assert!(exp == -13);
    ///
    ///     float.assign(0);
    ///     let (zero, _) = float.to_integer_exp().unwrap();
    ///     assert!(zero == 0);
    ///
    ///     float.assign(Special::Infinity);
    ///     assert!(float.to_integer_exp().is_none());
    /// }
    /// ```
    pub fn to_integer_exp(&self) -> Option<(Integer, i32)> {
        if !self.is_finite() {
            return None;
        }
        let mut i = Integer::new();
        let exp = unsafe {
            mpfr::get_z_2exp(integer_inner_mut(&mut i), &self.inner) as i32
        };
        Some((i, exp))
    }

    /// Converts to a `u32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    pub fn to_u32_saturating(&self) -> Option<u32> {
        self.to_u32_saturating_round(Round::Nearest)
    }

    /// Converts to a `u32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    pub fn to_u32_saturating_round(&self, round: Round) -> Option<u32> {
        if self.is_nan() {
            return None;
        }
        let u = unsafe { mpfr::get_ui(&self.inner, rraw(round)) };
        if u >= u32::MAX as c_ulong {
            Some(u32::MAX)
        } else {
            Some(u as u32)
        }
    }

    /// Converts to an `i32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    pub fn to_i32_saturating(&self) -> Option<i32> {
        self.to_i32_saturating_round(Round::Nearest)
    }

    /// Converts to an `i32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    pub fn to_i32_saturating_round(&self, round: Round) -> Option<i32> {
        if self.is_nan() {
            return None;
        }
        let i = unsafe { mpfr::get_si(&self.inner, rraw(round)) };
        if i >= i32::MAX as c_long {
            Some(i32::MAX)
        } else if i <= i32::MIN as c_long {
            Some(i32::MIN)
        } else {
            Some(i as i32)
        }
    }

    /// Converts to an `f64`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    pub fn to_f64(&self) -> f64 {
        self.to_f64_round(Round::Nearest)
    }

    /// Converts to an `f64`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    pub fn to_f64_round(&self, round: Round) -> f64 {
        unsafe { mpfr::get_d(&self.inner, rraw(round)) }
    }

    /// Converts to an `f32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    pub fn to_f32(&self) -> f32 {
        self.to_f32_round(Round::Nearest)
    }

    /// Converts to an `f32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    pub fn to_f32_round(&self, round: Round) -> f32 {
        self.to_f64_round(round) as f32
    }

    math_op1! {
        "Computes the square, \
         rounding to the nearest.",
        square,
        "Computes the square, \
         applying the specified rounding method.",
        square_round,
        mpfr::sqr
    }
    math_op1! {
        "Computes the square root, \
         rounding to the nearest.",
        sqrt,
        "Computes the square root, \
         applying the specified rounding method.",
        sqrt_round,
        mpfr::sqrt
    }

    /// Sets `self` to the square root of `u`,
    /// rounding to the nearest.
    pub fn set_sqrt(&mut self, u: u32) -> &mut Float {
        self.set_sqrt_round(u, Round::Nearest);
        self
    }

    /// Sets `self` to the square root of `u`,
    /// applying the specified rounding method.
    pub fn set_sqrt_round(&mut self, u: u32, round: Round) -> Ordering {
        unsafe { mpfr::sqrt_ui(&mut self.inner, u.into(), rraw(round)).cmp(&0) }
    }

    math_op1! {
        "Computes the reciprocal square root, \
         rounding to the nearest.",
        recip_sqrt,
        "Computes the reciprocal square root, \
         applying the specified rounding method.",
        recip_sqrt_round,
        mpfr::rec_sqrt
    }
    math_op1! {
        "Computes the cube root, \
         rounding to the nearest.",
        cbrt,
        "Computes the cube root, \
         applying the specified rounding method.",
        cbrt_round,
        mpfr::cbrt
    }
    math_op1! {
        "Computes the `k`th root, \
         rounding to the nearest.",
        root,
        "Computes the `k`th root, \
         applying the specified rounding method.",
        root_round,
        mpfr::root,
        k: u32
    }

    /// Computes the absolute value,
    /// rounding to the nearest.
    pub fn abs(&mut self) -> &mut Float {
        unsafe {
            mpfr::abs(&mut self.inner, &self.inner, rraw(Round::Nearest));
        }
        self
    }

    /// Computes the reciprocal,
    /// rounding to the nearest.
    pub fn recip(&mut self) -> &mut Float {
        self.recip_round(Round::Nearest);
        self
    }

    /// Computes the reciprocal,
    /// applying the specified rounding method.
    pub fn recip_round(&mut self, round: Round) -> Ordering {
        unsafe {
            mpfr::ui_div(&mut self.inner, 1, &self.inner, rraw(round)).cmp(&0)
        }
    }

    math_op2! {
        "Computes the positive difference between `self` and `other`, \
         rounding to the nearest.",
        dim,
        "Computes the arithmetic-geometric mean of `self` and `other`, \
         applying the specified rounding method.",
        dim_round,
        mpfr::dim
    }

    /// Compares the absolute values of `self` and `other`.
    pub fn cmp_abs(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(&self.inner, &other.inner) {
                0 => Some(mpfr::cmpabs(&self.inner, &other.inner).cmp(&0)),
                _ => None,
            }
        }
    }

    math_op1! {
        "Computes the natural logarithm, \
         rounding to the nearest.",
        ln,
        "Computes the natural logarithm, \
         applying the specified rounding method.",
        ln_round,
        mpfr::log
    }
    math_op1! {
        "Computes the logarithm to base 2, \
         rounding to the nearest.",
        log2,
        "Computes the logarithm to base 2, \
         applying the specified rounding method.",
        log2_round,
        mpfr::log2
    }
    math_op1! {
        "Computes the logarithm to base 10, \
         rounding to the nearest.",
        log10,
        "Computes the logarithm to base 10, \
         applying the specified rounding method.",
        log10_round,
        mpfr::log10
    }
    math_op1! {
        "Computes the exponential, \
         rounding to the nearest.",
        exp,
        "Computes the exponential, \
         applying the specified rounding method.",
        exp_round,
        mpfr::exp
    }
    math_op1! {
        "Computes 2 to the power of `self`, \
         rounding to the nearest.",
        exp2,
        "Computes 2 to the power of `self`, \
         applying the specified rounding method.",
        exp2_round,
        mpfr::exp2
    }
    math_op1! {
        "Computes 10 to the power of `self`, \
         rounding to the nearest.",
        exp10,
        "Computes 10 to the power of `self`, \
         applying the specified rounding method.",
        exp10_round,
        mpfr::exp10
    }
    math_op1! {
        "Computes the cosine, \
         rounding to the nearest.",
        cos,
        "Computes the cosine, \
         applying the specified rounding method.",
        cos_round,
        mpfr::cos
    }
    math_op1! {
        "Computes the sine, \
         rounding to the nearest.",
        sin,
        "Computes the sine, \
         applying the specified rounding method.",
        sin_round,
        mpfr::sin
    }
    math_op1! {
        "Computes the tangent, \
         rounding to the nearest.",
        tan,
        "Computes the tangent, \
         applying the specified rounding method.",
        tan_round,
        mpfr::tan
    }

    /// Computes the sine and cosine, rounding to the nearest. The
    /// sine is stored in `self` and keeps its precision, while the
    /// cosine is stored in `buf` keeping its precision.
    pub fn sin_cos(&mut self, buf: &mut Float) {
        self.sin_cos_round(buf, Round::Nearest);
    }

    /// Computes the sine and cosine, applying the specified rounding
    /// method. The sine is stored in `self` and keeps its precision,
    /// while the cosine is stored in `buf` keeping its precision.
    pub fn sin_cos_round(&mut self,
                         buf: &mut Float,
                         round: Round)
                         -> (Ordering, Ordering) {
        let ord = unsafe {
            mpfr::sin_cos(&mut self.inner,
                          &mut buf.inner,
                          &self.inner,
                          rraw(round))
        };
        ordering2(ord)
    }

    math_op1! {
        "Computes the secant, \
         rounding to the nearest.",
        sec,
        "Computes the secant, \
         applying the specified rounding method.",
        sec_round,
        mpfr::sec
    }
    math_op1! {
        "Computes the cosecant, \
         rounding to the nearest.",
        csc,
        "Computes the cosecant, \
         applying the specified rounding method.",
        csc_round,
        mpfr::csc
    }
    math_op1! {
        "Computes the cotangent, \
         rounding to the nearest.",
        cot,
        "Computes the cotangent, \
         applying the specified rounding method.",
        cot_round,
        mpfr::cot
    }
    math_op1! {
        "Computes the arc-cosine, \
         rounding to the nearest.",
        acos,
        "Computes the arc-cosine, \
         applying the specified rounding method.",
        acos_round,
        mpfr::acos
    }
    math_op1! {
        "Computes the arc-sine, \
         rounding to the nearest.",
        asin,
        "Computes the arc-sine, \
         applying the specified rounding method.",
        asin_round,
        mpfr::asin
    }
    math_op1! {
        "Computes the arc-tangent, \
         rounding to the nearest.",
        atan,
        "Computes the arc-tangent, \
         applying the specified rounding method.",
        atan_round,
        mpfr::atan
    }
    math_op2! {
        "Computes the arc-tangent2 of `self` and `other`, \
         rounding to the nearest.\n\n\
         This is similar to the arc-tangent of `self / other`, \
         except in the cases when either `self` or `other` or both \
         are zero or infinity.",
        atan2,
        "Computes the arc-tangent2 of `self` and `other`, \
         applying the specified rounding method.\n\n\
         This is similar to the arc-tangent of `self / other`, \
         except in the cases when either `self` or `other` or both \
         are zero or infinity.",
        atan2_round,
        mpfr::atan2
    }
    math_op1! {
        "Computes the hyperbolic cosine, \
         rounding to the nearest.",
        cosh,
        "Computes the hyperbolic cosine, \
         applying the specified rounding method.",
        cosh_round,
        mpfr::cosh
    }
    math_op1! {
        "Computes the hyperbolic sine, \
         rounding to the nearest.",
        sinh,
        "Computes the hyperbolic sine, \
         applying the specified rounding method.",
        sinh_round,
        mpfr::sinh
    }
    math_op1! {
        "Computes the hyperbolic tangent, \
         rounding to the nearest.",
        tanh,
        "Computes the hyperbolic tangent, \
         applying the specified rounding method.",
        tanh_round,
        mpfr::tanh
    }

    /// Computes the hyperbolic sine and cosine, rounding to the
    /// nearest. The sine is stored in `self` and keeps its precision,
    /// while the cosine is stored in `buf` keeping its precision.
    pub fn sinh_cosh(&mut self, buf: &mut Float) {
        self.sinh_cosh_round(buf, Round::Nearest);
    }

    /// Computes the hyperbolic sine and cosine, applying the
    /// specified rounding method. The sine is stored in `self` and
    /// keeps its precision, while the cosine is stored in `buf`
    /// keeping its precision.
    pub fn sinh_cosh_round(&mut self,
                           buf: &mut Float,
                           round: Round)
                           -> (Ordering, Ordering) {
        let ord = unsafe {
            mpfr::sinh_cosh(&mut self.inner,
                            &mut buf.inner,
                            &self.inner,
                            rraw(round))
        };
        ordering2(ord)
    }

    math_op1! {
        "Computes the hyperbolic secant, \
         rounding to the nearest.",
        sech,
        "Computes the hyperbolic secant, \
         applying the specified rounding method.",
        sech_round,
        mpfr::sech
    }
    math_op1! {
        "Computes the hyperbolic cosecant, \
         rounding to the nearest.",
        csch,
        "Computes the hyperbolic cosecant, \
         applying the specified rounding method.",
        csch_round,
        mpfr::csch
    }
    math_op1! {
        "Computes the hyperbolic cotangent, \
         rounding to the nearest.",
        coth,
        "Computes the hyperbolic cotangent, \
         applying the specified rounding method.",
        coth_round,
        mpfr::coth
    }
    math_op1! {
        "Computes the inverse hyperbolic cosine, \
         rounding to the nearest.",
        acosh,
        "Computes the inverse hyperbolic cosine, \
         applying the specified rounding method.",
        acosh_round,
        mpfr::acosh
    }
    math_op1! {
        "Computes the inverse hyperbolic sine, \
         rounding to the nearest.",
        asinh,
        "Computes the inverse hyperbolic sine, \
         applying the specified rounding method.",
        asinh_round,
        mpfr::asinh
    }
    math_op1! {
        "Computes the inverse hyperbolic tangent, \
         rounding to the nearest.",
        atanh,
        "Computes the inverse hyperbolic tangent, \
         applying the specified rounding method.",
        atanh_round,
        mpfr::atanh
    }

    /// Sets `self` to the factorial of `u`,
    /// rounding to the nearest.
    pub fn set_factorial(&mut self, u: u32) -> &mut Float {
        self.set_factorial_round(u, Round::Nearest);
        self
    }

    /// Sets `self` to the factorial of `u`,
    /// applying the specified rounding method.
    pub fn set_factorial_round(&mut self, u: u32, round: Round) -> Ordering {
        unsafe { mpfr::fac_ui(&mut self.inner, u.into(), rraw(round)).cmp(&0) }
    }

    math_op1! {
        "Computes the natural logarithm of one plus `self`, \
         rounding to the nearest.",
        ln_1p,
        "Computes the natural logarithm of one plus `self`, \
         applying the specified rounding method.",
        ln_1p_round,
        mpfr::log1p
    }
    math_op1! {
        "Subtracts one from  the exponential of `self`, \
         rounding to the nearest.",
        exp_m1,
        "Subtracts one from  the exponential of `self`, \
         applying the specified rounding method.",
        exp_m1_round,
        mpfr::expm1
    }
    math_op1! {
        "Computes the exponential integral of `self`, \
         rounding to the nearest.",
        eint,
        "Computes the exponential integral of `self`, \
         applying the specified rounding method.",
        eint_round,
        mpfr::eint
    }
    math_op1! {
        "Computes the real part of the dilogarithm of `self`, \
         rounding to the nearest.",
        li2,
        "Computes the real part of the dilogarithm of `self`, \
         applying the specified rounding method.",
        li2_round,
        mpfr::li2
    }
    math_op1! {
        "Computes the value of the Gamma function on `self`, \
         rounding to the nearest.",
        gamma,
        "Computes the value of the Gamma function on `self`, \
         applying the specified rounding method.",
        gamma_round,
        mpfr::gamma
    }
    math_op1! {
        "Computes the logarithm of the Gamma function on `self`, \
         rounding to the nearest.",
        ln_gamma,
        "Computes the logarithm of the Gamma function on `self`, \
         applying the specified rounding method.",
        ln_gamma_round,
        mpfr::lngamma
    }

    /// Computes the logarithm of the absolute value of the Gamma
    /// function on `self`, rounding to the nearest. Returns
    /// `Ordering::Less` if the Gamma function is negative, or
    /// `Ordering::Greater` if the Gamma function is positive.
    pub fn lgamma(&mut self) -> Ordering {
        self.lgamma_round(Round::Nearest).0
    }

    /// Computes the logarithm of the absolute value of the Gamma
    /// function on `self`, applying the specified rounding method.
    /// The returned tuple contains:
    ///
    /// 1. The logarithm of the absolute value of the Gamma function.
    /// 2. The rounding direction.
    pub fn lgamma_round(&mut self, round: Round) -> (Ordering, Ordering) {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let ord = unsafe {
            mpfr::lgamma(&mut self.inner, sign_ptr, &self.inner, rraw(round))
                .cmp(&0)
        };
        let sign_ord = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        (sign_ord, ord)
    }

    math_op1! {
        "Computes the value of the Digamma function on `self`, \
         rounding to the nearest.",
        digamma,
        "Computes the value of the Digamma function on `self`, \
         applying the specified rounding method.",
        digamma_round,
        mpfr::digamma
    }
    math_op1! {
        "Computes the value of the Riemann Zeta function on `self`, \
         rounding to the nearest.",
        zeta,
        "Computes the value of the Riemann Zeta function on `self`, \
         applying the specified rounding method.",
        zeta_round,
        mpfr::zeta
    }

    /// Sets `self` to the value of the Riemann Zeta function on `u`,
    /// rounding to the nearest.
    pub fn set_zeta(&mut self, u: u32) -> &mut Float {
        self.set_zeta_round(u, Round::Nearest);
        self
    }

    /// Sets `self` to the value of the Riemann Zeta function on `u`,
    /// applying the specified rounding method.
    pub fn set_zeta_round(&mut self, u: u32, round: Round) -> Ordering {
        unsafe { mpfr::zeta_ui(&mut self.inner, u.into(), rraw(round)).cmp(&0) }
    }

    math_op1! {
        "Computes the value of the error function on `self`, \
         rounding to the nearest.",
        erf,
        "Computes the value of the error function on `self`, \
         applying the specified rounding method.",
        erf_round,
        mpfr::erf
    }
    math_op1! {
        "Computes the value of the complementary error function on `self`, \
         rounding to the nearest.",
        erfc,
        "Computes the value of the complementary error function on `self`, \
         applying the specified rounding method.",
        erfc_round,
        mpfr::erfc
    }
    math_op1! {
        "Computes the value of the first kind Bessel function of \
         order 0 on `self`, rounding to the nearest.",
        j0,
        "Computes the value of the first kind Bessel function of \
         order 0 on `self`, applying the specified rounding method.",
        j0_round,
        mpfr::j0
    }
    math_op1! {
        "Computes the value of the first kind Bessel function of \
         order 1 on `self`, rounding to the nearest.",
        j1,
        "Computes the value of the first kind Bessel function of \
         order 1 on `self`, applying the specified rounding method.",
        j1_round,
        mpfr::j1
    }
    math_op1! {
        "Computes the value of the first kind Bessel function of \
         order `n` on `self`, rounding to the nearest.",
        jn,
        "Computes the value of the first kind Bessel function of \
         order `n` on `self`, applying the specified rounding method.",
        jn_round,
        jn,
        n: i32
    }
    math_op1! {
        "Computes the value of the second kind Bessel function of \
         order 0 on `self`, rounding to the nearest.",
        y0,
        "Computes the value of the second kind Bessel function of \
         order 0 on `self`, applying the specified rounding method.",
        y0_round,
        mpfr::y0
    }
    math_op1! {
        "Computes the value of the second kind Bessel function of \
         order 1 on `self`, rounding to the nearest.",
        y1,
        "Computes the value of the second kind Bessel function of \
         order 1 on `self`, applying the specified rounding method.",
        y1_round,
        mpfr::y1
    }
    math_op1! {
        "Computes the value of the second kind Bessel function of \
         order `n` on `self`, rounding to the nearest.",
        yn,
        "Computes the value of the second kind Bessel function of \
         order `n` on `self`, applying the specified rounding method.",
        yn_round,
        yn,
        n: i32
    }
    math_op2! {
        "Computes the arithmetic-geometric mean of `self` and `other`, \
         rounding to the nearest.",
        agm,
        "Computes the arithmetic-geometric mean of `self` and `other`, \
         applying the specified rounding method.",
        agm_round,
        mpfr::agm
    }
    math_op2! {
        "Computes the Euclidean norm of `self` and `other`, \
         rounding to the nearest.",
        hypot,
        "Computes the Euclidean norm of `self` and `other`, \
         applying the specified rounding method.",
        hypot_round,
        mpfr::hypot
    }
    math_op1! {
        "Computes the value of the Airy function Ai on `self`, \
         rounding to the nearest.",
        ai,
        "Computes the value of the Airy function Ai on `self`, \
         applying the specified rounding method.",
        ai_round,
        mpfr::ai
    }
    math_op1! {
        "Rounds up to the next higher integer, then rounds to the \
         nearest. This function performs double rounding.",
        ceil,
        "Rounds up to the next higher integer, then applies the \
         specified rounding method. \
         This function performs double rounding.",
        ceil_round,
        mpfr::rint_ceil
    }
    math_op1! {
        "Rounds down to the next lower integer, then rounds to the \
         nearest. This function performs double rounding.",
        floor,
        "Rounds down to the next lower integer, then applies the \
         specified rounding method. \
         This function performs double rounding.",
        floor_round,
        mpfr::rint_floor
    }
    math_op1! {
        "Rounds to the nearest integer, rounding half-way cases away \
         from zero, then rounds to the nearest representable value. \
         This function performs double rounding.",
        round,
        "Rounds to the next lower integer, then applies the \
         specified rounding method to get a representable value.
         This function performs double rounding.",
        round_round,
        mpfr::rint_round
    }
    math_op1! {
        "Rounds to the next integer towards zero, then rounds to the \
         nearest. This function performs double rounding.",
        trunc,
        "Rounds to the next integer towards zero, then applies the \
         specified rounding method. \
         This function performs double rounding.",
        trunc_round,
        mpfr::rint_trunc
    }

    /// Returns `true` if `self` is an integer.
    pub fn is_integer(&self) -> bool {
        unsafe { mpfr::integer_p(&self.inner) != 0 }
    }

    /// Returns `true` if `self` is not a number.
    pub fn is_nan(&self) -> bool {
        unsafe { mpfr::nan_p(&self.inner) != 0 }
    }

    /// Returns `true` if `self` is plus or minus infinity.
    pub fn is_infinite(&self) -> bool {
        unsafe { mpfr::inf_p(&self.inner) != 0 }
    }

    /// Returns `true` if `self` is a finite number,
    /// that is neither NaN nor infinity.
    pub fn is_finite(&self) -> bool {
        unsafe { mpfr::number_p(&self.inner) != 0 }
    }

    /// Returns `true` if `self` is plus or minus zero.
    pub fn is_zero(&self) -> bool {
        unsafe { mpfr::zero_p(&self.inner) != 0 }
    }

    /// Returns `true` if `self` is a normal number, that is neither
    /// NaN, nor infinity, nor zero. Note that `Float` cannot be
    /// subnormal.
    pub fn is_normal(&self) -> bool {
        unsafe { mpfr::regular_p(&self.inner) != 0 }
    }

    /// Returns `Less` if `self` is less than zero,
    /// `Greater` if `self` is greater than zero,
    /// or `Equal` if `self` is equal to zero.
    pub fn sign(&self) -> Option<Ordering> {
        if self.is_nan() {
            None
        } else {
            Some(unsafe { mpfr::sgn(&self.inner).cmp(&0) })
        }
    }

    /// Returns the exponent of `self` if `self` is a normal number,
    /// otherwise `None`.
    /// The significand is assumed to be in the range [0.5,1).
    pub fn get_exp(&self) -> Option<i32> {
        if self.is_normal() {
            let e = unsafe { mpfr::get_exp(&self.inner) };
            assert!(e <= i32::MAX as mpfr::exp_t, "overflow");
            Some(e as i32)
        } else {
            None
        }
    }

    /// Returns the sign bit, that is `true` if the number is negative.
    pub fn get_sign(&self) -> bool {
        unsafe { mpfr::signbit(&self.inner) != 0 }
    }

    /// Emulate subnormal numbers, rounding to the nearest. This
    /// method has no effect if the value is not in the subnormal
    /// range.
    pub fn subnormalize(&mut self) -> &mut Float {
        self.subnormalize_round(Ordering::Equal, Round::Nearest);
        self
    }

    /// Emulate subnormal numbers, applying the specified rounding
    /// method. This method simply propagates `prev_rounding` if the
    /// value is not in the subnormal range.
    pub fn subnormalize_round(&mut self,
                              prev_rounding: Ordering,
                              round: Round)
                              -> Ordering {
        let prev = match prev_rounding {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        };
        unsafe {
            mpfr::subnormalize(&mut self.inner, prev, rraw(round)).cmp(&0)
        }
    }

    #[cfg(feature = "random")]
    /// Generates a random number in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, Round::Nearest)`]
    /// (#method.assign_random_bits_round).
    pub fn assign_random_bits<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_bits_round(rng, Round::Nearest);
    }

    #[cfg(feature = "random")]
    /// Generates a random number in the range `0 <= n < 1`.
    ///
    /// This is equivalent to generating a random integer in the range
    /// `0 <= n < 2 ^ p`, where `2 ^ p` is two raised to the power of
    /// the precision, and then dividing the integer by `2 ^ p`. The
    /// smallest non-zero result will thus be `2 ^ -p`, and will only
    /// have one bit set. In the smaller possible results, many bits
    /// will be zero, and not all the precision will be used.
    ///
    /// In all the normal cases, the result will be exact. However, if
    /// the precision is very large, and the generated random number
    /// is very small, this may require an exponent smaller than
    /// `rugflo::exp_min()`; in this case, rounding is applied and
    /// the rounding direction is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugflo;
    /// use rugflo::{Float, Round};
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let mut f = Float::new(2);
    ///     f.assign_random_bits_round(&mut rng, Round::Nearest);
    ///     assert!(f == 0.0 || f == 0.25 || f == 0.5 || f == 0.75);
    ///     println!("0.0 <= {} < 1.0", f);
    /// }
    /// ```
    pub fn assign_random_bits_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round)
                                            -> Ordering {
        let limb_bits = gmp::LIMB_BITS as usize;
        let bits = self.inner.prec as usize;
        let whole_limbs = bits / limb_bits;
        let extra_bits = bits % limb_bits;
        // Avoid conditions and overflow, equivalent to:
        // let total_limbs = whole_limbs + if extra_bits == 0 { 0 } else { 1 };
        let total_limbs = whole_limbs +
                          (extra_bits + limb_bits - 1) / limb_bits;
        let limbs =
            unsafe { slice::from_raw_parts_mut(self.inner.d, total_limbs) };
        let mut lead_zeros = total_limbs * limb_bits;
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut val: gmp::limb_t = rng.gen();
            if i == 0 && extra_bits > 0 {
                let all_ones: gmp::limb_t = !0;
                val &= all_ones << (limb_bits - extra_bits);
            }
            if val != 0 {
                lead_zeros = (total_limbs - 1 - i) * limb_bits +
                             val.leading_zeros() as usize;
            }
            *limb = val;
        }
        let zero_limbs = lead_zeros / limb_bits as usize;
        if zero_limbs == total_limbs {
            unsafe {
                mpfr::set_zero(&mut self.inner, 0);
            }
            return Ordering::Equal;
        }
        let zero_bits = (lead_zeros % limb_bits) as c_uint;
        let err = unsafe {
            mpfr::set_exp(&mut self.inner, -(lead_zeros as mpfr::exp_t))
        };
        if err != 0 {
            // This is extremely unlikely, we can be inefficient.
            // Firs set MSB, then subtract by 0.5
            let high_one: gmp::limb_t = 1 << (limb_bits - 1);
            limbs[total_limbs - 1] |= high_one;
            let ord = unsafe {
                mpfr::set_exp(&mut self.inner, 0);
                mpfr::sub_d(&mut self.inner, &self.inner, 0.5, rraw(round))
            };
            return ord.cmp(&0);
        }
        if zero_bits > 0 {
            let ptr_offset = zero_limbs as isize;
            unsafe {
                gmp::mpn_lshift(self.inner.d.offset(ptr_offset),
                                self.inner.d,
                                (total_limbs - zero_limbs) as gmp::size_t,
                                zero_bits);
            }
        } else if zero_limbs > 0 {
            for i in (zero_limbs..total_limbs).rev() {
                limbs[i] = limbs[i - zero_limbs];
            }
        }
        for limb in limbs.iter_mut().take(zero_limbs) {
            *limb = 0;
        }
        Ordering::Equal
    }

    #[cfg(feature = "random")]
    /// Generates a random number in the continuous range
    /// `0 <= n < 1`, and rounds to the nearest.
    ///
    /// The rounded result can actually be equal to one.
    /// This is equivalent to calling
    /// [`assign_random_cont_round(rng, Round::Nearest)`]
    /// (#method.assign_random_cont_round).
    pub fn assign_random_cont<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_cont_round(rng, Round::Nearest);
    }

    #[cfg(feature = "random")]
    /// Generates a random number in the continous range
    /// `0 <= n < 1` and applies the specified rounding method.
    ///
    /// The rounded result can actually be equal to one. Unlike
    /// [`assign_random_bits_round()`](#method.assign_random_bits_round)
    /// which generates a discrete random number at intervals
    /// depending on the precision, this method is equivalent to
    /// generating a continuous random number with infinite precision
    /// and then rounding the result. This means that even the smaller
    /// numbers will be using all the available precision bits, and
    /// rounding is performed in all cases, not in some corner case.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugflo;
    /// use rugflo::{Float, Round};
    /// use std::cmp::Ordering;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let mut f = Float::new(2);
    ///     let dir = f.assign_random_cont_round(&mut rng, Round::Nearest);
    ///     // We cannot have an exact value without rounding.
    ///     assert!(dir != Ordering::Equal);
    ///     // The significand is either 0b10 or 0b11
    ///     //           10          11
    ///     assert!(f == 1.0 || f == 0.75 ||
    ///             f == 0.5 || f == 0.375 ||
    ///             f == 0.25 || f <= 0.1875);
    ///     // If the result is 1.0, rounding was up.
    ///     assert!(f != 1.0 || dir == Ordering::Greater);
    /// }
    /// ```
    pub fn assign_random_cont_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round)
                                            -> Ordering {
        let limb_bits = gmp::LIMB_BITS as usize;
        let bits = self.inner.prec as usize;
        let total_limbs = (bits + limb_bits - 1) / limb_bits;
        let limbs =
            unsafe { slice::from_raw_parts_mut(self.inner.d, total_limbs) };
        // If exp is too small, random_cont_first_limb will
        // have the result.
        if let Some(ret) = self.random_cont_first_limb(bits, rng, round) {
            return ret;
        }
        for limb in limbs.iter_mut().skip(1) {
            *limb = rng.gen();
        }
        let high_one: gmp::limb_t = 1 << (limb_bits - 1);
        let spare_bit = (limbs[total_limbs - 1] & high_one) != 0;
        limbs[total_limbs - 1] |= high_one;
        let down = match round {
            Round::Down | Round::Zero => true,
            Round::Up | Round::AwayFromZero => false,
            Round::Nearest => spare_bit,
        };
        if down {
            return Ordering::Less;
        }
        unsafe {
            mpfr::nextabove(&mut self.inner);
        }
        Ordering::Greater
    }

    #[cfg(feature = "random")]
    fn random_cont_first_limb<R: Rng>(&mut self,
                                      bits: usize,
                                      rng: &mut R,
                                      round: Round)
                                      -> Option<Ordering> {
        let limb_bits = gmp::LIMB_BITS as usize;
        let mut exp: i32 = 0;
        let mut val: gmp::limb_t;
        let mut zeros;
        loop {
            val = rng.gen();
            zeros = val.leading_zeros() as i32;
            // if exp too small, return ~0
            if exp < exp_min() + zeros {
                unsafe {
                    mpfr::set_zero(&mut self.inner, 0);
                }
                let down = match round {
                    Round::Down | Round::Zero => true,
                    Round::Up | Round::AwayFromZero => false,
                    Round::Nearest => {
                        exp + 1 < exp_min() + zeros ||
                        (zeros as usize == limb_bits && rng.gen::<bool>())
                    }
                };
                if down {
                    return Some(Ordering::Less);
                }
                unsafe {
                    mpfr::nextabove(&mut self.inner);
                }
                return Some(Ordering::Greater);
            }
            exp -= zeros;
            if val != 0 {
                unsafe {
                    mpfr::set_exp(&mut self.inner, exp.into());
                }
                break;
            }
        }
        // increment zero to ignore msb, which we know is one
        zeros += 1;
        // fill the least significant limb
        let bits_in_lsl = (bits - 1) % limb_bits + 1;
        if limb_bits < bits_in_lsl + zeros as usize {
            val = rng.gen();
        }
        val <<= limb_bits - bits_in_lsl;
        unsafe {
            *self.inner.d = val;
        }
        None
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` rounding to the nearest.
    ///
    /// The exponent is encoded in decimal. The output string will have
    /// enough precision such that reading it again will give the exact
    /// same number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::{Float, Special};
    /// let neg_inf = Float::from((Special::MinusInfinity, 53));
    /// assert!(neg_inf.to_string_radix(10, None) == "-inf");
    /// assert!(neg_inf.to_string_radix(16, None) == "-@inf@");
    /// let fifteen = Float::from((15, 8));
    /// assert!(fifteen.to_string_radix(10, None) == "1.500e1");
    /// assert!(fifteen.to_string_radix(16, None) == "f.00@0");
    /// assert!(fifteen.to_string_radix(10, Some(2)) == "1.5e1");
    /// assert!(fifteen.to_string_radix(16, Some(4)) == "f.000@0");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self,
                           radix: i32,
                           num_digits: Option<usize>)
                           -> String {
        self.to_string_radix_round(radix, num_digits, Round::Nearest)
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` applying the specified rounding method.
    ///
    /// The exponent is encoded in decimal. The output string will have
    /// enough precision such that reading it again will give the exact
    /// same number.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix_round(&self,
                                 radix: i32,
                                 num_digits: Option<usize>,
                                 round: Round)
                                 -> String {
        make_string(self, radix, num_digits, round, false)
    }

    /// Parses a `Float` with the specified precision, rounding to the
    /// nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    pub fn from_str(src: &str, prec: u32) -> Result<Float, ParseFloatError> {
        let mut f = Float::new(prec);
        f.assign_str(src)?;
        Ok(f)
    }

    /// Parses a `Float` with the specified radix and precision,
    /// rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str,
                          radix: i32,
                          prec: u32)
                          -> Result<Float, ParseFloatError> {
        let mut f = Float::new(prec);
        f.assign_str_radix(src, radix)?;
        Ok(f)
    }

    /// Parses a `Float` with the specified precision, applying the
    /// specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_round).
    pub fn from_str_round(src: &str,
                          prec: u32,
                          round: Round)
                          -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new(prec);
        let ord = f.assign_str_round(src, round)?;
        Ok((f, ord))
    }

    /// Parses a `Float` with the specified radix and precision,
    /// applying the specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix_round).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix_round
        (src: &str,
         radix: i32,
         prec: u32,
         round: Round)
         -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new(prec);
        let ord = f.assign_str_radix_round(src, radix, round)?;
        Ok((f, ord))
    }

    /// Parses a `Float` from a string, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::Float;
    /// let mut f = Float::new(53);
    /// f.assign_str("12.5e2").unwrap();
    /// assert!(f == 12.5e2);
    /// let ret = f.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseFloatError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Float` from a string with the specified radix,
    /// rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::Float;
    /// let mut f = Float::new(53);
    /// f.assign_str_radix("f.f", 16).unwrap();
    /// assert!(f == 15.9375);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ParseFloatError> {
        self.assign_str_radix_round(src, radix, Round::Nearest)
            .map(|_| ())
    }

    /// Parses a `Float` from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rugflo::{Float, Round};
    /// use std::cmp::Ordering;
    /// let mut f = Float::new(4);
    /// let dir = f.assign_str_round("14.1", Round::Down).unwrap();
    /// assert!(f == 14);
    /// assert!(dir == Ordering::Less);
    /// ```
    pub fn assign_str_round(&mut self,
                            src: &str,
                            round: Round)
                            -> Result<Ordering, ParseFloatError> {
        self.assign_str_radix_round(src, 10, round)
    }

    /// Parses a `Float` from a string with the specified radix,
    /// applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rugflo::{Float, Round};
    /// use std::cmp::Ordering;
    /// let mut f = Float::new(4);
    /// let dir = f.assign_str_radix_round("e.c", 16, Round::Up).unwrap();
    /// assert!(f == 15);
    /// assert!(dir == Ordering::Greater);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix_round(&mut self,
                                  src: &str,
                                  radix: i32,
                                  round: Round)
                                  -> Result<Ordering, ParseFloatError> {

        let c_str = match check_str_radix(src, radix, true)? {
            PossibleFromStr::Owned(s) => CString::new(s).unwrap(),
            PossibleFromStr::Borrowed(s) => CString::new(s).unwrap(),
            PossibleFromStr::Special(s) => {
                self.assign(s);
                return Ok(Ordering::Equal);
            }
        };
        let mut c_str_end: *const c_char = ptr::null();
        let ord = unsafe {
            mpfr::strtofr(&mut self.inner,
                          c_str.as_ptr(),
                          &mut c_str_end as *mut _ as *mut *mut c_char,
                          radix as c_int,
                          rraw(round))
                    .cmp(&0)
        };
        let nul = c_str.as_bytes_with_nul().last().unwrap() as *const _ as
                  *const c_char;
        assert!(c_str_end == nul);
        Ok(ord)
    }

    /// Checks if a `Float` can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Float`. If this method returns
    /// an error, the other functions will return the same error.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(src: &str,
                           radix: i32)
                           -> Result<(), ParseFloatError> {
        check_str_radix(src, radix, false).map(|_| ())
    }
}

enum PossibleFromStr<'a> {
    Owned(String),
    Borrowed(&'a str),
    Special(Special),
}

// If will_use_returned is false, do not allocate as the result will
// be discarded anyway.
fn check_str_radix(src: &str,
                   radix: i32,
                   will_use_returned: bool)
                   -> Result<PossibleFromStr, ParseFloatError> {
    use self::ParseFloatError as Error;
    use self::ParseErrorKind as Kind;

    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let (inf10, neg_inf10, nan10) = (&["inf", "+inf", "infinity", "+infinity"],
                                     &["-inf", "-infinity"],
                                     &["nan", "+nan", "-nan"]);
    let (inf, neg_inf, nan) =
        (&["@inf@", "+@inf@", "@infinity@", "+@infinity@"],
         &["-@inf@", "-@infinity@"],
         &["@nan@", "+@nan@", "-@nan@"]);
    if (radix <= 10 && lcase_in(src, inf10)) || lcase_in(src, inf) {
        return Ok(PossibleFromStr::Special(Special::Infinity));
    }
    if (radix <= 10 && lcase_in(src, neg_inf10)) || lcase_in(src, neg_inf) {
        return Ok(PossibleFromStr::Special(Special::MinusInfinity));
    }
    if (radix <= 10 && lcase_in(src, nan10)) || lcase_in(src, nan) {
        return Ok(PossibleFromStr::Special(Special::Nan));
    }

    let mut char_indices = src.char_indices();
    let starts_with_plus = src.starts_with('+');
    if starts_with_plus || src.starts_with('-') {
        char_indices.next();
    }
    let mut got_digit = false;
    let mut got_point = false;
    let mut exp = false;
    let mut fresh_exp = false;
    let mut buf = None;
    for (pos, c) in char_indices {
        if fresh_exp {
            fresh_exp = false;
            if c == '-' {
                continue;
            }
            if c == '+' {
                if will_use_returned {
                    // CString should use extra byte for nul.
                    let mut s = String::with_capacity(src.len());
                    let begin_index = if starts_with_plus { 1 } else { 0 };
                    s.push_str(&src[begin_index..pos]);
                    s.push_str(&src[pos + 1..]);
                    buf = Some(s);
                }
                continue;
            }
        }
        if c == '.' {
            if exp {
                return Err(Error { kind: Kind::PointInExp });
            }
            if got_point {
                return Err(Error { kind: Kind::TooManyPoints });
            }
            got_point = true;
            continue;
        }
        if (radix <= 10 && (c == 'e' || c == 'E')) || c == '@' {
            if exp {
                return Err(Error { kind: Kind::TooManyExp });
            }
            if !got_digit {
                return Err(Error { kind: Kind::SignifNoDigits });
            }
            got_digit = false;
            exp = true;
            fresh_exp = true;
            continue;
        }
        let digit_value = match c {
            '0'...'9' => c as i32 - '0' as i32,
            'a'...'z' => c as i32 - 'a' as i32 + 10,
            'A'...'Z' => c as i32 - 'A' as i32 + 10,
            _ => Err(Error { kind: Kind::InvalidDigit })?,
        };
        if (!exp && digit_value >= radix) || (exp && digit_value >= 10) {
            return Err(Error { kind: Kind::InvalidDigit });
        }
        got_digit = true;
    }
    if !got_digit && exp {
        return Err(Error { kind: Kind::ExpNoDigits });
    } else if !got_digit {
        return Err(Error { kind: Kind::NoDigits });
    }
    if let Some(buf) = buf {
        Ok(PossibleFromStr::Owned(buf))
    } else if starts_with_plus {
        Ok(PossibleFromStr::Borrowed(&src[1..]))
    } else {
        Ok(PossibleFromStr::Borrowed(src))
    }
}

unsafe fn jn(rop: *mut mpfr_t,
             op: *const mpfr_t,
             n: i32,
             rnd: mpfr::rnd_t)
             -> c_int {
    mpfr::jn(rop, n.into(), op, rnd)
}

unsafe fn yn(rop: *mut mpfr_t,
             op: *const mpfr_t,
             n: i32,
             rnd: mpfr::rnd_t)
             -> c_int {
    mpfr::yn(rop, n.into(), op, rnd)
}

impl<T> From<(T, i32)> for Float
    where Float: From<(T, u32)>
{
    fn from((t, prec): (T, i32)) -> Float {
        assert!(prec >= prec_min() as i32, "precision out of range");
        Float::from((t, prec as u32))
    }
}

impl<T> FromRound<T, i32> for Float
    where Float: FromRound<T, u32, Round = Round, Ordering = Ordering>
{
    type Round = Round;
    type Ordering = Ordering;
    fn from_round(t: T, prec: i32, round: Round) -> (Float, Ordering) {
        assert!(prec >= prec_min() as i32, "precision out of range");
        Float::from_round(t, prec as u32, round)
    }
}

macro_rules! from_borrow {
    { $d:expr, $t:ty } => {
        impl<'a> From<(&'a $t, u32)> for Float {
            /// Constructs a `Float` from
            #[doc=$d]
            /// with the specified precision, rounding to the nearest.
            fn from((t, prec): (&'a $t, u32)) -> Float {
                let mut ret = Float::new(prec);
                ret.assign(t);
                ret
            }
        }

        impl<'a> FromRound<&'a $t, u32> for Float {
            type Round = Round;
            type Ordering = Ordering;

            /// Constructs a `Float` from
            #[doc=$d]
            /// with the specified precision, applying the specified
            /// rounding method.
            fn from_round(t: &'a $t, prec: u32, round: Round)
                          -> (Float, Ordering) {
                let mut ret = Float::new(prec);
                let ord = ret.assign_round(t, round);
                (ret, ord)
            }
        }
    };
}

macro_rules! from {
    { $d:expr, $t:ty } => {
        impl From<($t, u32)> for Float {
            /// Constructs a `Float` from
            #[doc=$d]
            /// with the specified precision, rounding to the nearest.
            fn from((t, prec): ($t, u32)) -> Float {
                Float::from_round(t, prec, Round::Nearest).0
            }
        }

        impl FromRound<$t, u32> for Float {
            type Round = Round;
            type Ordering = Ordering;

            /// Constructs a `Float` from
            #[doc=$d]
            /// with the specified precision, applying the specified
            /// rounding method.
            fn from_round(t: $t, prec: u32, round: Round)
                          -> (Float, Ordering) {
                let mut ret = Float::new(prec);
                let ord = ret.assign_round(t, round);
                (ret, ord)
            }
        }
    };
}

from! { "a `Constant`", Constant }
from! { "a `Special`", Special }
from! { "an `Integer`", Integer }
from! { "a `Rational` number", Rational }
from! { "another `Float`", Float }
from_borrow! { "an `Integer`", Integer }
from_borrow! { "a `Rational` number", Rational }
from_borrow! { "another `Float", Float }
from! { "a `u32`", u32 }
from! { "an `i32`", i32 }
from! { "an `f64`", f64 }
from! { "an `f32`", f32 }

impl Assign<Constant> for Float {
    /// Assigns from a `Constant` and rounds to the nearest.
    fn assign(&mut self, other: Constant) {
        self.assign_round(other, Round::Nearest);
    }
}

impl AssignRound<Constant> for Float {
    type Round = Round;
    type Ordering = Ordering;
    /// Assigns from a `Constant` and applies the specified rounding
    /// method.
    fn assign_round(&mut self, other: Constant, round: Round) -> Ordering {
        let mpfr_ret = unsafe {
            match other {
                Constant::Log2 => {
                    mpfr::const_log2(&mut self.inner, rraw(round))
                }
                Constant::Pi => mpfr::const_pi(&mut self.inner, rraw(round)),
                Constant::Euler => {
                    mpfr::const_euler(&mut self.inner, rraw(round))
                }
                Constant::Catalan => {
                    mpfr::const_catalan(&mut self.inner, rraw(round))
                }
            }
        };
        mpfr_ret.cmp(&0)
    }
}

impl Assign<Special> for Float {
    /// Assigns from a `Special`.
    fn assign(&mut self, other: Special) {
        unsafe {
            match other {
                Special::Zero => mpfr::set_zero(&mut self.inner, 0),
                Special::MinusZero => mpfr::set_zero(&mut self.inner, -1),
                Special::Infinity => mpfr::set_inf(&mut self.inner, 0),
                Special::MinusInfinity => mpfr::set_inf(&mut self.inner, -1),
                Special::Nan => mpfr::set_nan(&mut self.inner),
            };
        }
    }
}

impl AssignRound<Special> for Float {
    type Round = Round;
    type Ordering = Ordering;
    /// Assigns from a `Special`.
    fn assign_round(&mut self, other: Special, _round: Round) -> Ordering {
        self.assign(other);
        Ordering::Equal
    }
}

macro_rules! assign {
    { $d:expr, $t:ty, $eval:expr } => {
        impl<'a> Assign<&'a $t> for Float {
            /// Assigns from
            #[doc=$d]
            /// and rounds to the nearest.
            fn assign(&mut self, other: &'a $t) {
                self.assign_round(other, Round::Nearest);
            }
        }

        impl<'a> AssignRound<&'a $t> for Float {
            type Round = Round;
            type Ordering = Ordering;

            /// Assigns from
            #[doc=$d]
            /// and applies the specified rounding method.
            fn assign_round(&mut self, other: &'a $t, round: Round)
                            -> Ordering {
                $eval(&mut self.inner, other, rraw(round)).cmp(&0)
            }
        }

        impl Assign<$t> for Float {
            /// Assigns from
            #[doc=$d]
            /// and rounds to the nearest.
            fn assign(&mut self, other: $t) {
                self.assign_round(&other, Round::Nearest);
            }
        }

        impl AssignRound<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;

            /// Assigns from
            #[doc=$d]
            /// and applies the specified rounding method.
            fn assign_round(&mut self, other: $t, round: Round) -> Ordering {
                self.assign_round(&other, round)
            }
        }
    };
}

assign! { "another `Float`", Float,
           |f, t: &Float, r| unsafe { mpfr::set(f, &t.inner, r) } }
assign! { "an `Integer`", Integer,
           |f, t, r| unsafe { mpfr::set_z(f, integer_inner(t), r) } }
assign! { "a `Rational` number", Rational,
           |f, t, r| unsafe { mpfr::set_q(f, rational_inner(t), r) } }

impl<'a> Assign<&'a Float> for Integer {
    /// Assigns from a `Float`, rounding towards zero.
    fn assign(&mut self, val: &'a Float) {
        unsafe {
            mpfr::get_z(integer_inner_mut(self), &val.inner, rraw(Round::Zero));
        }
    }
}

impl<'a> Assign<Float> for Integer {
    /// Assigns from a `Float`, rounding towards zero.
    fn assign(&mut self, val: Float) {
        self.assign(&val);
    }
}

impl<'a> From<&'a Float> for Rational {
    /// <a id="rational_from_float"></a>
    /// Constructs a `Rational` number from a `Float`,
    /// preserving all the precision of the value.
    /// The value must not be a NaN or infinite.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugrat;
    /// extern crate rugflo;
    /// use rugrat::Rational;
    /// use rugflo::{Float, FromRound, Round};
    /// use std::str::FromStr;
    /// use std::cmp::Ordering;
    ///
    /// fn main() {
    ///     // Consider the number 123,456,789 / 10,000,000,000.
    ///     let res = Float::from_str_round("0.0123456789", 35, Round::Down);
    ///     let (f, f_rounding) = res.unwrap();
    ///     assert!(f_rounding == Ordering::Less);
    ///     let r = Rational::from_str("123456789/10000000000").unwrap();
    ///     // Set fr to the value of f exactly.
    ///     let fr = Rational::from(&f);
    ///     // Since f == fr and f was rounded down, r != fr.
    ///     assert!(r != fr);
    ///     let res = Float::from_round(&fr, 35, Round::Down);
    ///     let (frf, frf_rounding) = res;
    ///     assert!(frf_rounding == Ordering::Equal);
    ///     assert!(frf == f);
    ///     assert!(format!("{:.9}", frf) == "1.23456789e-2");
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `val` is a NaN or infinite.
    fn from(val: &Float) -> Rational {
        let (num, exp) = val.to_integer_exp().unwrap();
        Rational::from(num) << exp
    }
}

impl From<Float> for Rational {
    /// Constructs a `Rational` number from a `Float`,
    /// preserving all the precision of the value.
    /// The value must not be a NaN or infinite.
    /// See the [borrowing implementor](#rational_from_float).
    ///
    /// # Panics
    ///
    /// Panics if `val` is a NaN or infinite.
    fn from(val: Float) -> Rational {
        Rational::from(&val)
    }
}

impl<'a> Assign<&'a Float> for Rational {
    /// <a id="rational_assign_float"></a>
    /// Assigns from a `Float`,
    /// preserving all the precision of the value.
    /// The value must not be a NaN or infinite.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugrat;
    /// extern crate rugflo;
    /// use rugint::Assign;
    /// use rugrat::Rational;
    /// use rugflo::Float;
    ///
    /// fn main() {
    ///     let large_f = Float::from((6.5, 16));
    ///     let mut large_r = Rational::new();
    ///     large_r.assign(&large_f); // borrow
    ///     let small_f = Float::from((-0.125, 16));
    ///     let mut small_r = Rational::new();
    ///     small_r.assign(small_f); // move
    ///
    ///     assert!(*large_r.numer() == 13);
    ///     assert!(*large_r.denom() == 2);
    ///     assert!(*small_r.numer() == -1);
    ///     assert!(*small_r.denom() == 8);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `val` is a NaN or infinite.
    fn assign(&mut self, val: &'a Float) {
        assert!(val.is_finite());
        let exp = {
            let mut num_den = self.as_mut_numer_denom();
            num_den.1.assign(1);
            unsafe {
                mpfr::get_z_2exp(integer_inner_mut(num_den.0), &val.inner)
            }
        };
        *self <<= exp as i32;
    }
}

impl<'a> Assign<Float> for Rational {
    /// Assigns from a `Float`,
    /// preserving all the precision of the value.
    /// The value must not be a NaN or infinite.
    /// See the [`borrowing implementor`](#rational_assign_float).
    ///
    /// # Panics
    ///
    /// Panics if `val` is a NaN or infinite.
    fn assign(&mut self, val: Float) {
        self.assign(&val);
    }
}

macro_rules! arith_for_float {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $eval:expr) => {
        impl<'a> $imp<&'a $t> for Float {
            type Output = Float;
            fn $method(self, rhs: &'a $t) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $imp<$t> for Float {
            type Output = Float;
            fn $method(self, rhs: $t) -> Float {
                self.$method(&rhs)
            }
        }

        impl<'a> $imp_round<&'a $t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(mut self, rhs: &'a $t, round: Round)
                             -> (Float, Ordering) {
                let ord = $eval(&mut self.inner, rhs, rraw(round)).cmp(&0);
                (self, ord)
            }
        }

        impl $imp_round<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, rhs: $t, round: Round)
                             -> (Float, Ordering) {
                self.$method_round(&rhs, round)
            }
        }

        impl<'a> $imp_assign<&'a $t> for Float {
            fn $method_assign(&mut self, rhs: &'a $t) {
                $eval(&mut self.inner, rhs, rraw(Round::Nearest));
            }
        }

        impl $imp_assign<$t> for Float {
            fn $method_assign(&mut self, rhs: $t) {
                self.$method_assign(&rhs);
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
        arith_for_float! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $eval
        }

        impl $imp<Float> for $t {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $imp_round<Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, rhs: Float, round: Round)
                             -> (Float, Ordering) {
                rhs.$method_round(self, round)
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
        arith_for_float! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $eval
        }

        impl $imp<Float> for $t {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $imp_round<Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, mut rhs: Float, round: Round)
                             -> (Float, Ordering) {
                let ord = $eval_from(&mut rhs.inner, &self, rraw(round))
                    .cmp(&0);
                (rhs, ord)
            }
        }

        impl<'a> $imp_from_assign<&'a $t> for Float {
            fn $method_from_assign(&mut self, lhs: &'a $t) {
                $eval_from(&mut self.inner, lhs, rraw(Round::Nearest));
            }
        }

        impl $imp_from_assign<$t> for Float {
            fn $method_from_assign(&mut self, lhs: $t) {
                self.$method_from_assign(&lhs);
            }
        }
    };
}

arith_for_float! { Add add, AddRound add_round, AddAssign add_assign, Float,
                   |f, t: &Float, r| unsafe { mpfr::add(f, f, &t.inner, r) } }
arith_for_float! { Sub sub, SubRound sub_round, SubAssign sub_assign, Float,
                   |f, t: &Float, r| unsafe { mpfr::sub(f, f, &t.inner, r) } }

impl<'a> SubFromAssign<&'a Float> for Float {
    fn sub_from_assign(&mut self, lhs: &Float) {
        unsafe {
            mpfr::sub(&mut self.inner,
                      &lhs.inner,
                      &self.inner,
                      rraw(Round::Nearest));
        }
    }
}

impl SubFromAssign for Float {
    fn sub_from_assign(&mut self, lhs: Float) {
        self.sub_from_assign(&lhs);
    }
}

arith_for_float! { Mul mul, MulRound mul_round, MulAssign mul_assign, Float,
                   |f, t: &Float, r| unsafe { mpfr::mul(f, f, &t.inner, r) } }
arith_for_float! { Div div, DivRound div_round, DivAssign div_assign, Float,
                   |f, t: &Float, r| unsafe { mpfr::div(f, f, &t.inner, r) } }

impl<'a> DivFromAssign<&'a Float> for Float {
    fn div_from_assign(&mut self, lhs: &Float) {
        unsafe {
            mpfr::div(&mut self.inner,
                      &lhs.inner,
                      &self.inner,
                      rraw(Round::Nearest));
        }
    }
}

impl DivFromAssign for Float {
    fn div_from_assign(&mut self, lhs: Float) {
        self.div_from_assign(&lhs);
    }
}

arith_commut! { Add add, AddRound add_round, AddAssign add_assign, Integer,
                |f, t, r| unsafe { mpfr::add_z(f, f, integer_inner(t), r) } }
arith_non_commut! { Sub sub, SubRound sub_round, SubAssign sub_assign,
                    SubFromAssign sub_from_assign, Integer,
                  |f, t, r| unsafe  { mpfr::sub_z(f, f, integer_inner(t), r) },
                  |f, t, r| unsafe  { mpfr::z_sub(f, integer_inner(t), f, r) } }
arith_commut! { Mul mul, MulRound mul_round, MulAssign mul_assign, Integer,
                |f, t, r| unsafe { mpfr::mul_z(f, f, integer_inner(t), r) } }
arith_non_commut! { Div div, DivRound div_round, DivAssign div_assign,
                    DivFromAssign div_from_assign, Integer,
                    |f, t, r| unsafe { mpfr::div_z(f, f, integer_inner(t), r) },
                    |f, t, r| unsafe { z_div(t, f, r) } }

arith_commut! { Add add, AddRound add_round, AddAssign add_assign, Rational,
                |f, t, r| unsafe { mpfr::add_q(f, f, rational_inner(t), r) } }
arith_non_commut! { Sub sub, SubRound sub_round, SubAssign sub_assign,
                    SubFromAssign sub_from_assign, Rational,
                  |f, t, r| unsafe { mpfr::sub_q(f, f, rational_inner(t), r) },
                  |f, t, r| unsafe { q_sub(t, f, r) } }
arith_commut! { Mul mul, MulRound mul_round, MulAssign mul_assign, Rational,
                |f, t, r| unsafe { mpfr::mul_q(f, f, rational_inner(t), r) } }
arith_non_commut! { Div div, DivRound div_round, DivAssign div_assign,
                    DivFromAssign div_from_assign, Rational,
                  |f, t, r| unsafe { mpfr::div_q(f, f, rational_inner(t), r) },
                  |f, t, r| unsafe { q_div(t, f, r) } }

unsafe fn z_div(lhs: &Integer, rhs: *mut mpfr_t, rnd: mpfr::rnd_t) -> c_int {
    divf_mulz_divz(rhs, Some(lhs), None, rnd)
}

unsafe fn q_sub(lhs: &Rational, rhs: *mut mpfr_t, rnd: mpfr::rnd_t) -> c_int {
    let ret = -mpfr::sub_q(rhs, rhs, rational_inner(lhs), rnd);
    if mpfr::zero_p(rhs) == 0 {
        (*rhs).sign = -(*rhs).sign;
    }
    ret
}

unsafe fn q_div(lhs: &Rational, rhs: *mut mpfr_t, rnd: mpfr::rnd_t) -> c_int {
    let (lhs_num, lhs_den) = lhs.as_numer_denom();
    divf_mulz_divz(rhs, Some(lhs_num), Some(lhs_den), rnd)
}

// mul and div must must form a canonical rational, except that div
// can be negative
unsafe fn divf_mulz_divz(rop: *mut mpfr_t,
                         mul: Option<&Integer>,
                         div: Option<&Integer>,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    let mul_size = mul.map(|i| integer_inner(i).size);
    let div_size = div.map(|i| integer_inner(i).size);
    if mul_size == Some(0) {
        mpfr::ui_div(rop, 0, rop, rnd);
        if let Some(s) = div_size {
            if s < 0 {
                (*rop).sign = -(*rop).sign;
            }
        }
        return 0;
    }
    if div_size == Some(0) {
        mpfr::mul_ui(rop, rop, 0, rnd);
        mpfr::ui_div(rop, 1, rop, rnd);
        if let Some(s) = mul_size {
            if s < 0 {
                (*rop).sign = -(*rop).sign;
            }
        }
        return 0;
    }

    let mut denom_buf: Float;
    let denom = if let Some(div) = div {
        let mut prec = (*rop).prec as u32;
        assert!(prec as mpfr::prec_t == (*rop).prec, "overflow");
        prec = prec.checked_add(div.significant_bits()).expect("overflow");
        denom_buf = Float::new(prec);
        mpfr::mul_z(&mut denom_buf.inner,
                    rop,
                    integer_inner(div),
                    mpfr::rnd_t::RNDN);
        &denom_buf.inner as *const _
    } else {
        rop
    };
    if let Some(mul) = mul {
        let mut buf = Float::new(cmp::max(prec_min(), mul.significant_bits()));
        buf.assign(mul);
        mpfr::div(rop, &buf.inner, denom, rnd)
    } else {
        mpfr::ui_div(rop, 1, denom, rnd)
    }
}

macro_rules! sh_op {
    { $doc:expr,
      $imp:ident $method:ident,
      $imp_round:ident $method_round:ident,
      $imp_assign:ident $method_assign:ident,
      $t:ty,
      $func:path } => {
        impl $imp<$t> for Float {
            type Output = Float;
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, rounding to the
            /// nearest.
            fn $method(self, op: $t) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl $imp_round<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, applying the
            /// specified rounding.
            fn $method_round(mut self, op: $t, round: Round)
                             -> (Float, Ordering) {
                let ord = unsafe {
                    $func(&mut self.inner,
                          &self.inner,
                          op.into(),
                          rraw(round))
                        .cmp(&0)
                };
                (self, ord)
            }
        }

        impl $imp_assign<$t> for Float {
            #[doc=$doc]
            /// `self` by 2 to the power of `op`, rounding to the
            /// nearest.
            fn $method_assign(&mut self, op: $t) {
                unsafe {
                    $func(&mut self.inner,
                          &self.inner,
                          op.into(),
                          rraw(Round::Nearest));
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
    mpfr::mul_2ui
}
sh_op! {
    "Divides",
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    u32,
    mpfr::div_2ui
}
sh_op! {
    "Multiplies",
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    i32,
    mpfr::mul_2si
}
sh_op! {
    "Divides",
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    i32,
    mpfr::div_2si
}

macro_rules! pow_others {
    { $($t:ty)* } => { $(
        impl<'a> Pow<&'a $t> for Float {
            type Output = Float;
            fn pow(self, op: &'a $t) -> Float {
                self.pow_round(op, Round::Nearest).0
            }
        }

        impl Pow<$t> for Float {
            type Output = Float;
            fn pow(self, op: $t) -> Float {
                self.pow_round(op, Round::Nearest).0
            }
        }

        impl PowRound<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn pow_round(self, op: $t, round: Round) -> (Float, Ordering) {
                self.pow_round(&op, round)
            }
        }

        impl PowAssign<$t> for Float {
            fn pow_assign(&mut self, op: $t) {
                self.pow_assign(&op);
            }
        }
    )* };
}

impl<'a> PowRound<&'a Float> for Float {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(mut self, op: &'a Float, round: Round) -> (Float, Ordering) {
        let ord = unsafe {
            mpfr::pow(&mut self.inner, &self.inner, &op.inner, rraw(round))
                .cmp(&0)
        };
        (self, ord)
    }
}

impl<'a> PowAssign<&'a Float> for Float {
    fn pow_assign(&mut self, op: &'a Float) {
        unsafe {
            mpfr::pow(&mut self.inner,
                      &self.inner,
                      &op.inner,
                      rraw(Round::Nearest))
        };
    }
}

impl<'a> PowRound<&'a Integer> for Float {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(mut self, op: &'a Integer, round: Round) -> (Float, Ordering) {
        let ord = unsafe {
            mpfr::pow_z(&mut self.inner,
                        &self.inner,
                        integer_inner(op),
                        rraw(round))
                    .cmp(&0)
        };
        (self, ord)
    }
}

impl<'a> PowAssign<&'a Integer> for Float {
    fn pow_assign(&mut self, op: &'a Integer) {
        unsafe {
            mpfr::pow_z(&mut self.inner,
                        &self.inner,
                        integer_inner(op),
                        rraw(Round::Nearest));
        }
    }
}

pow_others! { Float Integer }

macro_rules! arith_prim_for_float {
    ($imp:ident $method:ident,
     $imp_round:ident $method_round:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $func:path) => {
        impl $imp<$t> for Float {
            type Output = Float;
            fn $method(self, op: $t) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl $imp_round<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(mut self, op: $t, round: Round)
                             -> (Float, Ordering) {
                let ord = unsafe {
                    $func(&mut self.inner,
                          &self.inner,
                          op.into(),
                          rraw(round))
                        .cmp(&0)
                };
                (self, ord)
            }
        }

        impl $imp_assign<$t> for Float {
            fn $method_assign(&mut self, op: $t) {
                unsafe {
                    $func(&mut self.inner,
                          &self.inner,
                          op.into(),
                          rraw(Round::Nearest));
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
        arith_prim_for_float! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Float> for $t {
            type Output = Float;
            fn $method(self, op: Float) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl<'a> $imp<&'a Float> for $t {
            type Output = Float;
            fn $method(self, op: &'a Float) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl $imp_round<Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, mut op: Float, round: Round)
                             -> (Float, Ordering) {
                let ord = unsafe {
                    $func_from(&mut op.inner,
                               self.into(),
                               &op.inner,
                               rraw(round))
                        .cmp(&0)
                };
                (op, ord)
            }
        }

        impl<'a> $imp_round<&'a Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, op: &'a Float, round: Round)
                             -> (Float, Ordering) {
                self.$method_round(op.clone(), round)
            }
        }

        impl $imp_from_assign<$t> for Float {
            fn $method_from_assign(&mut self, lhs: $t) {
                unsafe {
                    $func_from(&mut self.inner,
                               lhs.into(),
                               &self.inner,
                               rraw(Round::Nearest));
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
        arith_prim_for_float! {
            $imp $method,
            $imp_round $method_round,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Float> for $t {
            type Output = Float;
            fn $method(self, op: Float) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl<'a> $imp<&'a Float> for $t {
            type Output = Float;
            fn $method(self, op: &'a Float) -> Float {
                self.$method_round(op, Round::Nearest).0
            }
        }

        impl $imp_round<Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, op: Float, round: Round)
                             -> (Float, Ordering) {
                op.$method_round(self, round)
            }
        }

        impl<'a> $imp_round<&'a Float> for $t {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, op: &'a Float, round: Round)
                             -> (Float, Ordering) {
                self.$method_round(op.clone(), round)
            }
        }
    };
}

macro_rules! conv_ops {
    { ($t:ty, $set:path),
      ($add:path, $sub: path, $sub_from: path),
      ($mul:path, $div: path, $div_from: path) } => {
        impl Assign<$t> for Float {
            fn assign(&mut self, val: $t) {
                self.assign_round(val, Round::Nearest);
            }
        }

        impl AssignRound<$t> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(&mut self, val: $t, round: Round) -> Ordering {
                unsafe {
                    $set(&mut self.inner, val.into(), rraw(round)).cmp(&0)
                }
            }
        }

        arith_prim_commut! {
            Add add,
            AddRound add_round,
            AddAssign add_assign,
            $t,
            $add
        }
        arith_prim_non_commut! {
            Sub sub,
            SubRound sub_round,
            SubAssign sub_assign,
            SubFromAssign sub_from_assign,
            $t,
            $sub,
            $sub_from
        }
        arith_prim_commut! {
            Mul mul,
            MulRound mul_round,
            MulAssign mul_assign,
            $t,
            $mul
        }
        arith_prim_non_commut! {
            Div div,
            DivRound div_round,
            DivAssign div_assign,
            DivFromAssign div_from_assign,
            $t,
            $div,
            $div_from
        }
    }
}

conv_ops! {
    (u32, mpfr::set_ui),
    (mpfr::add_ui, mpfr::sub_ui, mpfr::ui_sub),
    (mpfr::mul_ui, mpfr::div_ui, mpfr::ui_div)
}
conv_ops! {
    (i32, mpfr::set_si),
    (mpfr::add_si, mpfr::sub_si, mpfr::si_sub),
    (mpfr::mul_si, mpfr::div_si, mpfr::si_div)
}
conv_ops! {
    (f64, mpfr::set_d),
    (mpfr::add_d, mpfr::sub_d, mpfr::d_sub),
    (mpfr::mul_d, mpfr::div_d, mpfr::d_div)
}
conv_ops! {
    (f32, set_single),
    (add_single, sub_single, single_sub),
    (mul_single, div_single, single_div)
}

macro_rules! cast_op {
    {
        $( $name:ident = mpfr::$func:ident(
            $($before:ident: $before_ty:ty),*;
            $op:ident;
            $($after:ident: $after_ty:ty),*
        ) -> $ret_ty:ty;)*
    } => {
        $(
            unsafe fn $name($($before: $before_ty),*,
                            $op: f32,
                            $($after: $after_ty),*)
                            -> $ret_ty {
                mpfr::$func($($before),*, $op as f64, $($after),*)
            }
        )*
    };
}
cast_op! {
    set_single = mpfr::set_d(rop: *mut mpfr_t;
                             op;
                             rnd: mpfr::rnd_t) -> c_int;
    add_single = mpfr::add_d(rop: *mut mpfr_t, op1: *const mpfr_t;
                             op2;
                             rnd: mpfr::rnd_t) -> c_int;
    sub_single = mpfr::sub_d(rop: *mut mpfr_t, op1: *const mpfr_t;
                             op2;
                             rnd: mpfr::rnd_t) -> c_int;
    single_sub = mpfr::d_sub(rop: *mut mpfr_t;
                             op1;
                             op2: *const mpfr_t, rnd: mpfr::rnd_t) -> c_int;
    mul_single = mpfr::mul_d(rop: *mut mpfr_t, op1: *const mpfr_t;
                             op2;
                             rnd: mpfr::rnd_t) -> c_int;
    div_single = mpfr::div_d(rop: *mut mpfr_t, op1: *const mpfr_t;
                             op2;
                             rnd: mpfr::rnd_t) -> c_int;
    single_div = mpfr::d_div(rop: *mut mpfr_t;
                             op1;
                             op2: *const mpfr_t, rnd: mpfr::rnd_t) -> c_int;
}

impl Pow<u32> for Float {
    type Output = Float;
    fn pow(self, op: u32) -> Float {
        self.pow_round(op, Round::Nearest).0
    }
}

impl Pow<Float> for u32 {
    type Output = Float;
    fn pow(self, op: Float) -> Float {
        self.pow_round(op, Round::Nearest).0
    }
}

impl<'a> Pow<&'a Float> for u32 {
    type Output = Float;
    fn pow(self, op: &'a Float) -> Float {
        self.pow_round(op, Round::Nearest).0
    }
}

impl PowRound<u32> for Float {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(mut self, op: u32, round: Round) -> (Float, Ordering) {
        let ord = unsafe {
            mpfr::pow_ui(&mut self.inner, &self.inner, op.into(), rraw(round))
                .cmp(&0)
        };
        (self, ord)
    }
}

impl PowRound<Float> for u32 {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(self, mut op: Float, round: Round) -> (Float, Ordering) {
        let ord = unsafe {
            mpfr::ui_pow(&mut op.inner, self.into(), &op.inner, rraw(round))
                .cmp(&0)
        };
        (op, ord)
    }
}

impl<'a> PowRound<&'a Float> for u32 {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(self, op: &'a Float, round: Round) -> (Float, Ordering) {
        self.pow_round(op.clone(), round)
    }
}

impl PowAssign<u32> for Float {
    fn pow_assign(&mut self, op: u32) {
        unsafe {
            mpfr::pow_ui(&mut self.inner,
                         &self.inner,
                         op.into(),
                         rraw(Round::Nearest))
        };
    }
}

impl Pow<i32> for Float {
    type Output = Float;
    fn pow(self, op: i32) -> Float {
        self.pow_round(op, Round::Nearest).0
    }
}

impl PowRound<i32> for Float {
    type Round = Round;
    type Ordering = Ordering;
    type Output = Float;
    fn pow_round(mut self, op: i32, round: Round) -> (Float, Ordering) {
        let ord = unsafe {
            mpfr::pow_si(&mut self.inner, &self.inner, op.into(), rraw(round))
                .cmp(&0)
        };
        (self, ord)
    }
}

impl PowAssign<i32> for Float {
    fn pow_assign(&mut self, op: i32) {
        unsafe {
            mpfr::pow_si(&mut self.inner,
                         &self.inner,
                         op.into(),
                         rraw(Round::Nearest))
        };
    }
}

impl Neg for Float {
    type Output = Float;
    fn neg(mut self) -> Float {
        self.neg_assign();
        self
    }
}

impl NegAssign for Float {
    fn neg_assign(&mut self) {
        unsafe {
            mpfr::neg(&mut self.inner, &self.inner, rraw(Round::Nearest));
        }
    }
}

impl PartialEq for Float {
    fn eq(&self, other: &Float) -> bool {
        unsafe { mpfr::equal_p(&self.inner, &other.inner) != 0 }
    }
}

impl PartialOrd for Float {
    /// Returns the ordering of `self` and `other`,
    /// or `None` if one (or both) of them is a NaN.
    fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(&self.inner, &other.inner) {
                0 => Some(mpfr::cmp(&self.inner, &other.inner).cmp(&0)),
                _ => None,
            }
        }
    }

    fn lt(&self, other: &Float) -> bool {
        unsafe { mpfr::less_p(&self.inner, &other.inner) != 0 }
    }

    fn le(&self, other: &Float) -> bool {
        unsafe { mpfr::lessequal_p(&self.inner, &other.inner) != 0 }
    }

    fn gt(&self, other: &Float) -> bool {
        unsafe { mpfr::greater_p(&self.inner, &other.inner) != 0 }
    }

    fn ge(&self, other: &Float) -> bool {
        unsafe { mpfr::greaterequal_p(&self.inner, &other.inner) != 0 }
    }
}

macro_rules! compare_common {
    { $t:ty, $eval:expr, $d_self:expr, $d_other:expr } => {
        impl PartialEq<$t> for Float {
            fn eq(&self, other: &$t) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$t> for Float {
            #[doc=$d_self]
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                if self.is_nan() {
                    return None;
                }
                Some($eval(&self.inner, other).cmp(&0))
            }
        }

        impl PartialEq<Float> for $t {
            fn eq(&self, other: &Float) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<Float> for $t {
            #[doc=$d_other]
            fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    }
}

macro_rules! compare_int {
    { $t:ty, $eval:expr } => {
        compare_common! {
            $t,
            $eval,
            "Returns the ordering of `self` and `other`, \
             or `None` if `self` is a NaN.",
            "Returns the ordering of `self` and `other`, \
             or `None` if `other` is a NaN."
        }
    };
}

macro_rules! compare_float {
    { $t:ty, $eval:expr } => {
        compare_common! {
            $t,
            $eval,
            "Returns the ordering of `self` and `other`, \
             or `None` if one (or both) of them is a NaN.",
            "Returns the ordering of `self` and `other`, \
             or `None` if one (or both) of them is a NaN."
        }
    };
}

compare_int! { Integer, |f, t| unsafe { mpfr::cmp_z(f, integer_inner(t)) } }
compare_int! { Rational, |f, t| unsafe { mpfr::cmp_q(f, rational_inner(t)) } }
compare_int! { u32, |f, t: &u32| unsafe { mpfr::cmp_ui(f, (*t).into()) } }
compare_int! { i32, |f, t: &i32| unsafe { mpfr::cmp_si(f, (*t).into()) } }
compare_float! { f64, |f, t: &f64| unsafe { mpfr::cmp_d(f, *t) } }
compare_float! { f32, |f, t: &f32| unsafe { mpfr::cmp_d(f, *t as f64) } }

fn make_string(f: &Float,
               radix: i32,
               precision: Option<usize>,
               round: Round,
               to_upper: bool)
               -> String {
    use std::fmt::Write;
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    if f.is_zero() {
        return "0.0".to_string();
    }
    if f.is_infinite() {
        return match (radix > 10, f.get_sign()) {
                   (false, false) => "inf".to_string(),
                   (false, true) => "-inf".to_string(),
                   (true, false) => "@inf@".to_string(),
                   (true, true) => "-@inf@".to_string(),
               };
    }
    if f.is_nan() {
        let s = if radix <= 10 { "NaN" } else { "@NaN@" };
        return s.to_string();
    }
    let mut buf = String::new();
    let mut exp: mpfr::exp_t;
    let digits = precision.map(|x| if x == 1 { 2 } else { x }).unwrap_or(0);
    let s;
    let cstr;
    unsafe {
        exp = mem::uninitialized();
        s = mpfr::get_str(ptr::null_mut(),
                          &mut exp,
                          radix.into(),
                          digits,
                          &f.inner,
                          rraw(round));
        assert!(!s.is_null());
        cstr = CStr::from_ptr(s);
    }
    let mut chars = cstr.to_str().unwrap().chars();
    let c = chars.next().unwrap();
    buf.push(char_to_upper_if(c, to_upper));
    if c == '-' {
        let c = chars.next().unwrap();
        buf.push(char_to_upper_if(c, to_upper));
    }
    buf.push('.');
    for c in chars {
        buf.push(char_to_upper_if(c, to_upper));
    }
    unsafe {
        mpfr::free_str(s);
    }
    buf.push(if radix <= 10 {
                 char_to_upper_if('e', to_upper)
             } else {
                 '@'
             });
    let exp = exp.checked_sub(1).expect("overflow");
    let _ = write!(buf, "{}", exp);
    buf
}

fn fmt_radix(flt: &Float,
             f: &mut Formatter,
             radix: i32,
             to_upper: bool,
             prefix: &str,
             show_neg_zero: bool)
             -> fmt::Result {
    let s = make_string(flt, radix, f.precision(), Round::Nearest, to_upper);
    if !flt.is_finite() {
        return f.pad(&s);
    }
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (show_neg_zero && flt.is_zero() && flt.get_sign(), &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

impl Display for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// An error which can be returned when parsing a `Float`.
pub struct ParseFloatError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    InvalidDigit,
    NoDigits,
    SignifNoDigits,
    ExpNoDigits,
    PointInExp,
    TooManyPoints,
    TooManyExp,
}

impl Error for ParseFloatError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidDigit => "invalid digit found in string",
            NoDigits => "string has no digits",
            SignifNoDigits => "string has no digits for significand",
            ExpNoDigits => "string has no digits for exponent",
            PointInExp => "string has point in exponent",
            TooManyPoints => "more than one point found in string",
            TooManyExp => "more than one exponent found in string",
        }
    }
}

impl Display for ParseFloatError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

fn integer_inner(z: &Integer) -> &gmp::mpz_t {
    let ptr = z as *const _ as *const gmp::mpz_t;
    unsafe { &*ptr }
}

unsafe fn integer_inner_mut(z: &mut Integer) -> &mut gmp::mpz_t {
    let ptr = z as *mut _ as *mut gmp::mpz_t;
    &mut *ptr
}

fn rational_inner(z: &Rational) -> &gmp::mpq_t {
    let ptr = z as *const _ as *const gmp::mpq_t;
    unsafe { &*ptr }
}

fn lcase_in(a: &str, bs: &[&str]) -> bool {
    'next_b: for b in bs {
        if a.len() != b.len() {
            continue 'next_b;
        }
        let acs = a.chars().map(|c| c.to_ascii_lowercase());
        let bcs = b.chars().map(|c| c.to_ascii_lowercase());
        for (ac, bc) in acs.zip(bcs) {
            if ac != bc {
                continue 'next_b;
            }
        }
        return true;
    }
    false
}

fn char_to_upper_if(c: char, to_upper: bool) -> char {
    if to_upper { c.to_ascii_uppercase() } else { c }
}

#[cfg(test)]
mod tests {
    use float::*;
    use std::{f32, f64};
    use std::str::FromStr;

    fn same(a: Float, b: Float) -> bool {
        if a.is_nan() && b.is_nan() {
            return true;
        }
        if a == b {
            return true;
        }
        if a.prec() == b.prec() {
            return false;
        }
        a == Float::from((b, a.prec()))
    }

    #[test]
    fn check_arith_others() {
        let work_prec = 20;
        let check_prec = 100;
        let f = [Float::from((Special::Zero, work_prec)),
                 Float::from((Special::MinusZero, work_prec)),
                 Float::from((Special::Infinity, work_prec)),
                 Float::from((Special::MinusInfinity, work_prec)),
                 Float::from((Special::Nan, work_prec)),
                 Float::from((1, work_prec)),
                 Float::from((-1, work_prec)),
                 Float::from((999999e100, work_prec)),
                 Float::from((999999e-100, work_prec)),
                 Float::from((-999999e100, work_prec)),
                 Float::from((-999999e-100, work_prec))];
        let z = [Integer::from(0),
                 Integer::from(1),
                 Integer::from(-1),
                 Integer::from_str("-1000000000000").unwrap(),
                 Integer::from_str("1000000000000").unwrap()];
        let q = [Rational::from(0),
                 Rational::from(1),
                 Rational::from(-1),
                 Rational::from_str("-1000000000000/33333333333").unwrap(),
                 Rational::from_str("1000000000000/33333333333").unwrap()];
        let u = [0, 1, 1000, u32::MAX];
        let s = [i32::MIN, -1000, -1, 0, 1, 1000, i32::MAX];
        let double = [f64::INFINITY,
                      f64::MAX,
                      f64::MIN_POSITIVE,
                      0.0,
                      -0.0,
                      -f64::MIN_POSITIVE,
                      f64::MIN,
                      f64::NEG_INFINITY,
                      f64::NAN,
                      1.0,
                      2.0,
                      12.0e43];
        let single = [f32::INFINITY,
                      f32::MAX,
                      f32::MIN_POSITIVE,
                      0.0,
                      -0.0,
                      -f32::MIN_POSITIVE,
                      f32::MIN,
                      f32::NEG_INFINITY,
                      f32::NAN,
                      1.0,
                      2.0,
                      12.0e30];
        for zz in &z {
            let zf = Float::from((zz, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + zz, ff.clone() + &zf));
                assert!(same(ff.clone() - zz, ff.clone() - &zf));
                assert!(same(ff.clone() * zz, ff.clone() * &zf));
                assert!(same(ff.clone() / zz, ff.clone() / &zf));
                assert!(same(zz.clone() + ff.clone(), zf.clone() + ff));
                assert!(same(zz.clone() - ff.clone(), zf.clone() - ff));
                assert!(same(zz.clone() * ff.clone(), zf.clone() * ff));
                assert!(same(zz.clone() / ff.clone(), zf.clone() / ff));
            }
        }
        for qq in &q {
            let qf = Float::from((qq, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + qq, ff.clone() + &qf));
                assert!(same(ff.clone() - qq, ff.clone() - &qf));
                assert!(same(ff.clone() * qq, ff.clone() * &qf));
                assert!(same(ff.clone() / qq, ff.clone() / &qf));
                assert!(same(qq.clone() + ff.clone(), qf.clone() + ff));
                assert!(same(qq.clone() - ff.clone(), qf.clone() - ff));
                assert!(same(qq.clone() * ff.clone(), qf.clone() * ff));
                assert!(same(qq.clone() / ff.clone(), qf.clone() / ff));
            }
        }
        for uu in &u {
            let uf = Float::from((*uu, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + *uu, ff.clone() + &uf));
                assert!(same(ff.clone() - *uu, ff.clone() - &uf));
                assert!(same(ff.clone() * *uu, ff.clone() * &uf));
                assert!(same(ff.clone() / *uu, ff.clone() / &uf));
                assert!(same(*uu + ff.clone(), uf.clone() + ff));
                assert!(same(*uu - ff.clone(), uf.clone() - ff));
                assert!(same(*uu * ff.clone(), uf.clone() * ff));
                assert!(same(*uu / ff.clone(), uf.clone() / ff));
            }
        }
        for ss in &s {
            let sf = Float::from((*ss, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + *ss, ff.clone() + &sf));
                assert!(same(ff.clone() - *ss, ff.clone() - &sf));
                assert!(same(ff.clone() * *ss, ff.clone() * &sf));
                assert!(same(ff.clone() / *ss, ff.clone() / &sf));
                assert!(same(*ss + ff.clone(), sf.clone() + ff));
                assert!(same(*ss - ff.clone(), sf.clone() - ff));
                assert!(same(*ss * ff.clone(), sf.clone() * ff));
                assert!(same(*ss / ff.clone(), sf.clone() / ff));
            }
        }
        for oo in &double {
            let of = Float::from((*oo, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
        for oo in &single {
            let of = Float::from((*oo, check_prec));
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
    }

    #[test]
    fn check_from_str() {
        assert!(Float::from_str_radix("-@nan@", 2, 53).unwrap().is_nan());
        assert!(Float::from_str("-0", 53).unwrap().get_sign());
        assert!(!Float::from_str("+0", 53).unwrap().get_sign());
        assert!(Float::from_str("1e1000", 53).unwrap().is_finite());
        let huge_hex = "1@99999999999999999999999999999999";
        assert!(Float::from_str_radix(huge_hex, 16, 53)
                    .unwrap()
                    .is_infinite());

        let bad_strings = [("inf", 16),
                           ("1e", 10),
                           ("e10", 10),
                           (".e10", 10),
                           ("1e1.", 10),
                           ("1e+-1", 10),
                           ("1e-+1", 10),
                           ("+-1", 10),
                           ("-+1", 10),
                           ("infinit", 10),
                           ("1@1a", 16),
                           ("9e0", 9)];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Float::valid_str_radix(s, radix).is_err());
        }
        let good_strings = [("INF", 10, f64::INFINITY),
                            ("-@iNf@", 16, f64::NEG_INFINITY),
                            ("+0e99", 2, 0.0),
                            ("-9.9e1", 10, -99.0),
                            ("-.99e+2", 10, -99.0),
                            ("+99.e+0", 10, 99.0),
                            ("-99@-1", 10, -9.9f64),
                            ("-abc.def@3", 16, -0xabcdef as f64),
                            ("1e1023", 2, 2.0f64.powi(1023))];
        for &(s, radix, f) in good_strings.into_iter() {
            assert!(Float::from_str_radix(s, radix, 53).unwrap() == f);
        }
    }

    #[test]
    fn check_formatting() {
        let mut f = Float::from((Special::Zero, 53));
        assert!(format!("{}", f) == "0.0");
        assert!(format!("{:?}", f) == "0.0");
        assert!(format!("{:+?}", f) == "+0.0");
        f.assign(Special::MinusZero);
        assert!(format!("{}", f) == "0.0");
        assert!(format!("{:?}", f) == "-0.0");
        assert!(format!("{:+?}", f) == "-0.0");
        f.assign(-27);
        assert!(format!("{:.2}", f) == "-2.7e1");
        assert!(format!("{:.4?}", f) == "-2.700e1");
        assert!(format!("{:.4e}", f) == "-2.700e1");
        assert!(format!("{:.4E}", f) == "-2.700E1");
        assert!(format!("{:.8b}", f) == "-1.1011000e4");
        assert!(format!("{:.3b}", f) == "-1.11e4");
        assert!(format!("{:#.8b}", f) == "-0b1.1011000e4");
        assert!(format!("{:.2o}", f) == "-3.3e1");
        assert!(format!("{:#.2o}", f) == "-0o3.3e1");
        assert!(format!("{:.2x}", f) == "-1.b@1");
        assert!(format!("{:.2X}", f) == "-1.B@1");
        assert!(format!("{:12.1x}", f) == "      -1.b@1");
        assert!(format!("{:012.3X}", f) == "-000001.B0@1");
        assert!(format!("{:#012.2x}", f) == "-0x00001.b@1");
        assert!(format!("{:#12.2X}", f) == "    -0x1.B@1");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert!(gmp::NAIL_BITS == 0);
        assert!(gmp::NUMB_BITS == gmp::LIMB_BITS);
        assert!(gmp::NUMB_BITS as usize == 8 * mem::size_of::<gmp::limb_t>());
    }
}
