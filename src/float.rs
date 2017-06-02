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
             PowFromAssign, SubFromAssign};
use rugrat::Rational;
use std::{i32, u32};
use std::ascii::AsciiExt;
use std::cmp::Ordering;
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
use xmpfr;

/// Returns the minimum value for the exponent.
pub fn exp_min() -> i32 {
    let min = unsafe { mpfr::get_emin() };
    if mem::size_of::<mpfr::exp_t>() <= mem::size_of::<i32>() ||
        min > i32::MIN as mpfr::exp_t
    {
        min as i32
    } else {
        i32::MIN
    }
}

/// Returns the maximum value for the exponent.
pub fn exp_max() -> i32 {
    let max = unsafe { mpfr::get_emax() };
    if mem::size_of::<mpfr::exp_t>() <= mem::size_of::<i32>() ||
        max < i32::MAX as mpfr::exp_t
    {
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
        max < u32::MAX as mpfr::prec_t
    {
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
    /// assert_eq!(f4, 24);
    /// f4.assign_round(27, Round::Nearest);
    /// assert_eq!(f4, 28);
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
/// assert_eq!(log2.to_string_radix(10, Some(5)), "6.9315e-1");
/// assert_eq!(pi.to_string_radix(10, Some(5)), "3.1416e0");
/// assert_eq!(euler.to_string_radix(10, Some(5)), "5.7722e-1");
/// assert_eq!(catalan.to_string_radix(10, Some(5)), "9.1597e-1");
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

impl Drop for Float {
    fn drop(&mut self) {
        unsafe {
            mpfr::clear(self.inner_mut());
        }
    }
}

macro_rules! math_op1 {
    {
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_hold:meta])*
        fn $method_hold:ident -> $Hold:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $($param: $T,)*
        ) -> &mut Float {
            self.$method_round(
                $($param,)*
                Round::Nearest,
            );
            self
        }

        $(#[$attr_round])*
        pub fn $method_round(
            &mut self,
            $($param: $T,)*
            round: Round,
        ) -> Ordering {
            let mpfr_ret = unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    rraw(round),
                )
            };
            mpfr_ret.cmp(&0)
        }

        $(#[$attr_hold])*
        pub fn $method_hold(
            &self,
            $($param: $T),*
        ) -> $Hold {
            $Hold {
                hold_self: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! hold_math_op1 {
    {
        $(#[$attr_hold:meta])*
        struct $Hold:ident { $($param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            hold_self: &'a Float,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Hold<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(
                &mut self,
                src: $Hold<'a>,
                round: Round,
            ) -> Ordering {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.hold_self.inner(),
                        $(src.$param.into(),)*
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
            }
        }
    };
}

macro_rules! math_op1_2 {
    {
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_hold:meta])*
        fn $method_hold:ident -> $Hold:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $rop: &mut Float,
            $($param: $T),*
        ) {
            self.$method_round(
                $rop,
                $($param,)*
                Round::Nearest,
            );
        }

        $(#[$attr_round])*
        pub fn $method_round(
            &mut self,
            $rop: &mut Float,
            $($param: $T,)*
            round: Round,
        ) -> (Ordering, Ordering) {
            let mpfr_ret = unsafe {
                $func(
                    self.inner_mut(),
                    $rop.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    rraw(round),
                )
            };
            ordering2(mpfr_ret)
        }

        $(#[$attr_hold])*
        pub fn $method_hold(
            &self,
            $($param: $T,)*
        ) -> $Hold {
            $Hold {
                hold_self: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! hold_math_op1_2 {
    {
        $(#[$attr_hold:meta])*
        struct $Hold:ident { $($param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            hold_self: &'a Float,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for (&'a mut Float, &'a mut Float) {
            fn assign(&mut self, src: $Hold<'a>) {
                self.assign_round(src, Round::Nearest);
            }
        }

        impl<'a> AssignRound<$Hold<'a>> for (&'a mut Float, &'a mut Float) {
            type Round = Round;
            type Ordering = (Ordering, Ordering);
            fn assign_round(
                &mut self,
                src: $Hold<'a>,
                round: Round,
            ) -> (Ordering, Ordering) {
                let mpfr_ret = unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.hold_self.inner(),
                        $(src.$param.into(),)*
                        rraw(round),
                    )
                };
                ordering2(mpfr_ret)
            }
        }
    };
}

macro_rules! math_op2 {
    {
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_hold:meta])*
        fn $method_hold:ident -> $Hold:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $op: &Float,
            $($param: $T,)*
        ) -> &mut Float {
            self.$method_round(
                $op,
                $($param.into(),)*
                Round::Nearest,
            );
            self
        }

        $(#[$attr_round])*
        pub fn $method_round(
            &mut self,
            $op: &Float,
            $($param: $T,)*
            round: Round,
        ) -> Ordering {
            let mpfr_ret = unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $op.inner(),
                    $($param.into(),)*
                    rraw(round),
                )
            };
            mpfr_ret.cmp(&0)
        }

        $(#[$attr_hold])*
        pub fn $method_hold<'a>(
            &'a self,
            $op: &'a Float,
            $($param: $T,)*
        ) -> $Hold<'a> {
            $Hold {
                hold_self: self,
                $op: $op,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! hold_math_op2 {
    {
        $(#[$attr_hold:meta])*
        struct $Hold:ident { $op:ident $(, $param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            hold_self: &'a Float,
            $op: &'a Float,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Hold<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(
                &mut self,
                src: $Hold<'a>,
                round: Round,
            ) -> Ordering {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.hold_self.inner(),
                        src.$op.inner(),
                        $(src.$param.into(),)*
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
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
        assert!(
            prec >= prec_min() && prec <= prec_max(),
            "precision out of range"
        );
        unsafe {
            let mut inner: mpfr_t = mem::uninitialized();
            mpfr::init2(&mut inner, prec as mpfr::prec_t);
            mpfr::set_zero(&mut inner, 0);
            Float { inner: inner }
        }
    }

    /// Returns the precision.
    pub fn prec(&self) -> u32 {
        unsafe { mpfr::get_prec(self.inner()) as u32 }
    }

    /// Sets the precision of `self`, rounding to the nearest.
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    pub fn set_prec(&mut self, prec: u32) {
        self.set_prec_round(prec, Round::Nearest);
    }

    /// Sets the precision of `self`, applying the specified
    /// rounding method.
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    pub fn set_prec_round(&mut self, prec: u32, round: Round) -> Ordering {
        assert!(
            prec >= prec_min() && prec <= prec_max(),
            "precision out of range"
        );
        let mpfr_ret = unsafe {
            mpfr::prec_round(
                self.inner_mut(),
                prec as mpfr::prec_t,
                rraw(round),
            )
        };
        mpfr_ret.cmp(&0)
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

    /// Parses a `Float` with the specified precision, applying the
    /// specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_round).
    pub fn from_str_round(
        src: &str,
        prec: u32,
        round: Round,
    ) -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new(prec);
        let ord = f.assign_str_round(src, round)?;
        Ok((f, ord))
    }

    /// Parses a `Float` with the specified radix and precision,
    /// rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(
        src: &str,
        radix: i32,
        prec: u32,
    ) -> Result<Float, ParseFloatError> {
        let mut f = Float::new(prec);
        f.assign_str_radix(src, radix)?;
        Ok(f)
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
        (
        src: &str,
        radix: i32,
        prec: u32,
        round: Round,
    ) -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new(prec);
        let ord = f.assign_str_radix_round(src, radix, round)?;
        Ok((f, ord))
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
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<(), ParseFloatError> {
        check_str_radix(src, radix, false).map(|_| ())
    }

    /// Converts to an integer, rounding to the nearest.
    pub fn to_integer(&self) -> Option<Integer> {
        self.to_integer_round(Round::Nearest).map(|x| x.0)
    }

    /// Converts to an integer, applying the specified rounding method.
    pub fn to_integer_round(
        &self,
        round: Round,
    ) -> Option<(Integer, Ordering)> {
        if !self.is_finite() {
            return None;
        }
        let mut i = Integer::new();
        let mpfr_ret =
            unsafe { mpfr::get_z(i.inner_mut(), self.inner(), rraw(round)) };
        Some((i, mpfr_ret.cmp(&0)))
    }

    /// If `self` is a [finite number](#method.is_finite), returns an
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
    ///     assert_eq!(int, 0b1101_0000_0000_0000);
    ///     assert_eq!(exp, -13);
    ///
    ///     float.assign(0);
    ///     let (zero, _) = float.to_integer_exp().unwrap();
    ///     assert_eq!(zero, 0);
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
        let exp =
            unsafe { mpfr::get_z_2exp(i.inner_mut(), self.inner()) as i32 };
        Some((i, exp))
    }

    /// If `self` is a [finite number](#method.is_finite), returns a
    /// `Rational` number preserving all the precision of the value.
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
    ///     assert_eq!(f_rounding, Ordering::Less);
    ///     let r = Rational::from_str("123456789/10000000000").unwrap();
    ///     // Set fr to the value of f exactly.
    ///     let fr = f.to_rational().unwrap();
    ///     // Since f == fr and f was rounded down, r != fr.
    ///     assert_ne!(r, fr);
    ///     let res = Float::from_round(&fr, 35, Round::Down);
    ///     let (frf, frf_rounding) = res;
    ///     assert_eq!(frf_rounding, Ordering::Equal);
    ///     assert_eq!(frf, f);
    ///     assert_eq!(format!("{:.9}", frf), "1.23456789e-2");
    /// }
    /// ```
    ///
    /// In the following example, the `Float` values can be
    /// represented exactly.
    ///
    /// ```rust
    /// use rugflo::Float;
    ///
    /// let large_f = Float::from((6.5, 16));
    /// let large_r = large_f.to_rational().unwrap();
    /// let small_f = Float::from((-0.125, 16));
    /// let small_r = small_f.to_rational().unwrap();
    ///
    /// assert_eq!(*large_r.numer(), 13);
    /// assert_eq!(*large_r.denom(), 2);
    /// assert_eq!(*small_r.numer(), -1);
    /// assert_eq!(*small_r.denom(), 8);
    /// ```
    pub fn to_rational(&self) -> Option<Rational> {
        self.to_integer_exp()
            .map(|(num, exp)| Rational::from(num) << exp)
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
        let i = unsafe { mpfr::get_si(self.inner(), rraw(round)) };
        if i >= i32::MAX as c_long {
            Some(i32::MAX)
        } else if i <= i32::MIN as c_long {
            Some(i32::MIN)
        } else {
            Some(i as i32)
        }
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
        let u = unsafe { mpfr::get_ui(self.inner(), rraw(round)) };
        if u >= u32::MAX as c_ulong {
            Some(u32::MAX)
        } else {
            Some(u as u32)
        }
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
        unsafe { mpfr::get_d(self.inner(), rraw(round)) }
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
    /// assert_eq!(neg_inf.to_string_radix(10, None), "-inf");
    /// assert_eq!(neg_inf.to_string_radix(16, None), "-@inf@");
    /// let fifteen = Float::from((15, 8));
    /// assert_eq!(fifteen.to_string_radix(10, None), "1.500e1");
    /// assert_eq!(fifteen.to_string_radix(16, None), "f.00@0");
    /// assert_eq!(fifteen.to_string_radix(10, Some(2)), "1.5e1");
    /// assert_eq!(fifteen.to_string_radix(16, Some(4)), "f.000@0");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(
        &self,
        radix: i32,
        num_digits: Option<usize>,
    ) -> String {
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
    pub fn to_string_radix_round(
        &self,
        radix: i32,
        num_digits: Option<usize>,
        round: Round,
    ) -> String {
        make_string(self, radix, num_digits, round, false)
    }

    /// Parses a `Float` from a string, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::Float;
    /// let mut f = Float::new(53);
    /// f.assign_str("12.5e2").unwrap();
    /// assert_eq!(f, 12.5e2);
    /// let ret = f.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseFloatError> {
        self.assign_str_radix(src, 10)
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
    /// assert_eq!(f, 14);
    /// assert_eq!(dir, Ordering::Less);
    /// ```
    pub fn assign_str_round(
        &mut self,
        src: &str,
        round: Round,
    ) -> Result<Ordering, ParseFloatError> {
        self.assign_str_radix_round(src, 10, round)
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
    /// assert_eq!(f, 15.9375);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseFloatError> {
        self.assign_str_radix_round(src, radix, Round::Nearest)
            .map(|_| ())
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
    /// assert_eq!(f, 15);
    /// assert_eq!(dir, Ordering::Greater);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix_round(
        &mut self,
        src: &str,
        radix: i32,
        round: Round,
    ) -> Result<Ordering, ParseFloatError> {

        let c_str = match check_str_radix(src, radix, true)? {
            PossibleFromStr::Owned(s) => CString::new(s).unwrap(),
            PossibleFromStr::Borrowed(s) => CString::new(s).unwrap(),
            PossibleFromStr::Special(s) => {
                self.assign(s);
                return Ok(Ordering::Equal);
            }
        };
        let mut c_str_end: *const c_char = ptr::null();
        let mpfr_ret = unsafe {
            mpfr::strtofr(
                self.inner_mut(),
                c_str.as_ptr(),
                &mut c_str_end as *mut _ as *mut *mut c_char,
                radix as c_int,
                rraw(round),
            )
        };
        let nul = c_str.as_bytes_with_nul().last().unwrap() as *const _ as
            *const c_char;
        assert_eq!(c_str_end, nul);
        Ok(mpfr_ret.cmp(&0))

    }

    /// Returns `true` if `self` is an integer.
    pub fn is_integer(&self) -> bool {
        unsafe { mpfr::integer_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is not a number.
    pub fn is_nan(&self) -> bool {
        unsafe { mpfr::nan_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus infinity.
    pub fn is_infinite(&self) -> bool {
        unsafe { mpfr::inf_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a finite number,
    /// that is neither NaN nor infinity.
    pub fn is_finite(&self) -> bool {
        unsafe { mpfr::number_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus zero.
    pub fn is_zero(&self) -> bool {
        unsafe { mpfr::zero_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a normal number, that is neither
    /// NaN, nor infinity, nor zero. Note that `Float` cannot be
    /// subnormal.
    pub fn is_normal(&self) -> bool {
        unsafe { mpfr::regular_p(self.inner()) != 0 }
    }

    /// Returns `Less` if `self` is less than zero,
    /// `Greater` if `self` is greater than zero,
    /// or `Equal` if `self` is equal to zero.
    pub fn sign(&self) -> Option<Ordering> {
        if self.is_nan() {
            None
        } else {
            let mpfr_ret = unsafe { mpfr::sgn(self.inner()) };
            Some(mpfr_ret.cmp(&0))
        }
    }

    /// Compares the absolute values of `self` and `other`.
    pub fn cmp_abs(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(mpfr::cmpabs(self.inner(), other.inner()).cmp(&0)),
                _ => None,
            }
        }
    }

    /// Returns the exponent of `self` if `self` is a normal number,
    /// otherwise `None`.
    /// The significand is assumed to be in the range [0.5,1).
    pub fn get_exp(&self) -> Option<i32> {
        if self.is_normal() {
            let e = unsafe { mpfr::get_exp(self.inner()) };
            assert!(e <= i32::MAX as mpfr::exp_t, "overflow");
            Some(e as i32)
        } else {
            None
        }
    }

    /// Returns the sign bit, that is `true` if the number is negative.
    pub fn get_sign(&self) -> bool {
        unsafe { mpfr::signbit(self.inner()) != 0 }
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
    pub fn subnormalize_round(
        &mut self,
        prev_rounding: Ordering,
        round: Round,
    ) -> Ordering {
        let prev = match prev_rounding {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        };
        let mpfr_ret =
            unsafe { mpfr::subnormalize(self.inner_mut(), prev, rraw(round)) };
        mpfr_ret.cmp(&0)
    }


    math_op1! {
        /// Computes the square, rounding to the nearest.
        fn square();
        /// Computes the square, applying the specified rounding method.
        fn square_round;
        /// Hold a computation of the square.
        fn square_hold -> SquareHold;
        mpfr::sqr
    }
    math_op1! {
        /// Computes the square root, rounding to the nearest.
        fn sqrt();
        /// Computes the square root, applying the specified rounding
        /// method.
        fn sqrt_round;
        /// Hold a computation of the square root.
        fn sqrt_hold -> SqrtHold;
        mpfr::sqrt
    }

    /// Sets `self` to the square root of `u`, rounding to the
    /// nearest.
    pub fn assign_sqrt_u(&mut self, u: u32) {
        self.assign_sqrt_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the square root of `u`, applying the specified
    /// rounding method.
    pub fn assign_sqrt_u_round(&mut self, u: u32, round: Round) -> Ordering {
        let mpfr_ret =
            unsafe { mpfr::sqrt_ui(self.inner_mut(), u.into(), rraw(round)) };
        mpfr_ret.cmp(&0)
    }

    math_op1! {
        /// Computes the reciprocal square root, rounding to the nearest.
        fn recip_sqrt();
        /// Computes the reciprocal square root, applying the specified
        /// rounding method.
        fn recip_sqrt_round;
        /// Hold a computation of the reciprocal square root.
        fn recip_sqrt_hold -> RecipSqrtHold;
        mpfr::rec_sqrt
    }
    math_op1! {
        /// Computes the cube root, rounding to the nearest.
        fn cbrt();
        /// Computes the cube root, applying the specified rounding
        /// method.
        fn cbrt_round;
        /// Hold a computation of the cube root.
        fn cbrt_hold -> CbrtHold;
        mpfr::cbrt
    }
    math_op1! {
        /// Computes the `k`th root, rounding to the nearest.
        fn root(k: u32);
        /// Computes the `k`th root, applying the specified rounding
        /// method.
        fn root_round;
        /// Hold a computation of the `k`th root.
        fn root_hold -> RootHold;
        mpfr::root
    }
    math_op1! {
        /// Computes the absolute value, rounding to the nearest.
        fn abs();
        /// Computes the absolute value, applying the specified rounding
        /// method.
        fn abs_round;
        /// Hold a computation of the absolute value.
        fn abs_hold -> AbsHold;
        mpfr::abs
    }
    math_op1! {
        /// Computes the reciprocal, rounding to the nearest.
        fn recip();
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        fn recip_round;
        /// Hold a computation of the reciprocal.
        fn recip_hold -> RecipHold;
        xmpfr::recip
    }
    math_op2! {
        /// Computes the positive difference between `self` and
        /// `other`, rounding to the nearest.
        fn abs_diff(other);
        /// Computes the positive difference between `self` and
        /// `other`, applying the specified rounding method.
        fn abs_diff_round;
        /// Hold a computation of the positive difference.
        fn abs_diff_hold -> AbsDiffHold;
        mpfr::dim
    }
    math_op1! {
        /// Computes the natural logarithm, rounding to the nearest.
        fn ln();
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        fn ln_round;
        /// Hold a computation of the natural logarithm.
        fn ln_hold -> LnHold;
        mpfr::log
    }
    math_op1! {
        /// Computes the logarithm to base 2, rounding to the nearest.
        fn log2();
        /// Computes the logarithm to base 2, applying the specified
        /// rounding method.
        fn log2_round;
        /// Hold a computation of the logarithm to base 2.
        fn log2_hold -> Log2Hold;
        mpfr::log2
    }
    math_op1! {
        /// Computes the logarithm to base 10, rounding to the nearest.
        fn log10();
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        fn log10_round;
        /// Hold a computation of the logarithm to base 10.
        fn log10_hold -> Log10Hold;
        mpfr::log10
    }
    math_op1! {
        /// Computes the exponential, rounding to the nearest.
        fn exp();
        /// Computes the exponential, applying the specified rounding
        /// method.
        fn exp_round;
        /// Hold a computation of the exponential.
        fn exp_hold -> ExpHold;
        mpfr::exp
    }
    math_op1! {
        /// Computes 2 to the power of `self`, rounding to the nearest.
        fn exp2();
        /// Computes 2 to the power of `self`, applying the specified
        /// rounding method.
        fn exp2_round;
        /// Hold a computation of 2 to power of the value.
        fn exp2_hold -> Exp2Hold;
        mpfr::exp2
    }
    math_op1! {
        /// Computes 10 to the power of `self`, rounding to the nearest.
        fn exp10();
        /// Computes 10 to the power of `self`, applying the specified
        /// rounding method.
        fn exp10_round;
        /// Hold a computation of 10 to the power of the value.
        fn exp10_hold -> Exp10Hold;
        mpfr::exp10
    }
    math_op1! {
        /// Computes the sine, rounding to the nearest.
        fn sin();
        /// Computes the sine, applying the specified rounding method.
        fn sin_round;
        /// Hold a computation of the sine.
        fn sin_hold -> SinHold;
        mpfr::sin
    }
    math_op1! {
        /// Computes the cosine, rounding to the nearest.
        fn cos();
        /// Computes the cosine, applying the specified rounding method.
        fn cos_round;
        /// Hold a computation of the cosine.
        fn cos_hold -> CosHold;
        mpfr::cos
    }
    math_op1! {
        /// Computes the tangent, rounding to the nearest.
        fn tan();
        /// Computes the tangent, applying the specified rounding method.
        fn tan_round;
        /// Hold a computation of the tangent.
        fn tan_hold -> TanHold;
        mpfr::tan
    }
    math_op1_2! {
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos(cos);
        /// Computes the sine and cosine of `self`, applying the specified
        /// rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos_round;
        /// Holds a computation of the sine and cosine.
        ///
        /// # Examples
        ///
        /// ```rust
        /// extern crate rugflo;
        /// extern crate rugint;
        /// use rugflo::Float;
        /// use rugint::Assign;
        ///
        /// fn main() {
        ///     // sin(0.5) = 0.47943, cos(0.5) = 0.87758
        ///     let angle = Float::from((0.5, 53));
        ///     let hold = angle.sin_cos_hold();
        ///     // use only 10 bits of precision here to
        ///     // make comparison easier
        ///     let (mut sin, mut cos) = (Float::new(10), Float::new(10));
        ///     (&mut sin, &mut cos).assign(hold);
        ///     assert_eq!(sin, Float::from((0.47943, 10)));
        ///     assert_eq!(cos, Float::from((0.87748, 10)));
        /// }
        fn sin_cos_hold -> SinCosHold;
        mpfr::sin_cos
    }
    math_op1! {
        /// Computes the secant, rounding to the nearest.
        fn sec();
        /// Computes the secant, applying the specified rounding method.
        fn sec_round;
        /// Hold a computation of the secant.
        fn sec_hold -> SecHold;
        mpfr::sec
    }
    math_op1! {
        /// Computes the cosecant, rounding to the nearest.
        fn csc();
        /// Computes the cosecant, applying the specified rounding method.
        fn csc_round;
        /// Hold a computation of the cosecant.
        fn csc_hold -> CscHold;
        mpfr::csc
    }
    math_op1! {
        /// Computes the cotangent, rounding to the nearest.
        fn cot();
        /// Computes the cotangent, applying the specified rounding
        /// method.
        fn cot_round;
        /// Hold a computation of the cotangent.
        fn cot_hold -> CotHold;
        mpfr::cot
    }
    math_op1! {
        /// Computes the arc-cosine, rounding to the nearest.
        fn acos();
        /// Computes the arc-cosine, applying the specified rounding
        /// method.
        fn acos_round;
        /// Hold a computation of the arc-cosine.
        fn acos_hold -> AcosHold;
        mpfr::acos
    }
    math_op1! {
        /// Computes the arc-sine, rounding to the nearest.
        fn asin();
        /// Computes the arc-sine, applying the specified rounding method.
        fn asin_round;
        /// Hold a computation of the arc-sine.
        fn asin_hold -> AsinHold;
        mpfr::asin
    }
    math_op1! {
        /// Computes the arc-tangent, rounding to the nearest.
        fn atan();
        /// Computes the arc-tangent, applying the specified rounding
        /// method.
        fn atan_round;
        /// Hold a computation of the arc-tangent.
        fn atan_hold -> AtanHold;
        mpfr::atan
    }
    math_op2! {
        /// Computes the arc-tangent2 of `self` and `other`, rounding to
        /// the nearest.
        ///
        /// This is similar to the arc-tangent of `self / other`, except
        /// in the cases when either `self` or `other` or both are zero or
        /// infinity.
        fn atan2(other);
        /// Computes the arc-tangent2 of `self` and `other`, applying the
        /// specified rounding method.
        ///
        /// This is similar to the arc-tangent of `self / other`, except
        /// in the cases when either `self` or `other` or both are zero or
        /// infinity.
        fn atan2_round;
        /// Hold a computation of the arc-tangent.
        fn atan2_hold -> Atan2Hold;
        mpfr::atan2
    }
    math_op1! {
        /// Computes the hyperbolic sine, rounding to the nearest.
        fn sinh();
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        fn sinh_round;
        /// Hold a computation of the hyperbolic sine.
        fn sinh_hold -> SinhHold;
        mpfr::sinh
    }
    math_op1! {
        /// Computes the hyperbolic cosine, rounding to the nearest.
        fn cosh();
        /// Computes the hyperbolic cosine, applying the specified
        /// rounding method.
        fn cosh_round;
        /// Hold a computation of the hyperbolic cosine.
        fn cosh_hold -> CoshHold;
        mpfr::cosh
    }
    math_op1! {
        /// Computes the hyperbolic tangent, rounding to the nearest.
        fn tanh();
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        fn tanh_round;
        /// Hold a computation of the hyperbolic tangent.
        fn tanh_hold -> TanhHold;
        mpfr::tanh
    }
    math_op1_2! {
        /// Computes the hyperbolic sine and cosine of `self`,
        /// rounding to the nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sinh_cosh(cos);
        /// Computes the hyperbolic sine and cosine of `self`,
        /// applying the specified rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sinh_cosh_round;
        /// Holds a computation of the hyperbolic sine and cosine.
        ///
        /// # Examples
        ///
        /// ```rust
        /// extern crate rugflo;
        /// extern crate rugint;
        /// use rugflo::Float;
        /// use rugint::Assign;
        ///
        /// fn main() {
        ///     // sinh(0.5) = 0.52110, cosh(0.5) = 1.1276
        ///     let angle = Float::from((0.5, 53));
        ///     let hold = angle.sinh_cosh_hold();
        ///     // use only 10 bits of precision here to
        ///     // make comparison easier
        ///     let (mut sinh, mut cosh) = (Float::new(10), Float::new(10));
        ///     (&mut sinh, &mut cosh).assign(hold);
        ///     assert_eq!(sinh, Float::from((0.52110, 10)));
        ///     assert_eq!(cosh, Float::from((1.1276, 10)));
        /// }
        fn sinh_cosh_hold -> SinhCoshHold;
        mpfr::sinh_cosh
    }
    math_op1! {
        /// Computes the hyperbolic secant, rounding to the nearest.
        fn sech();
        /// Computes the hyperbolic secant, applying the specified
        /// rounding method.
        fn sech_round;
        /// Hold a computation of the hyperbolic secant.
        fn sech_hold -> SechHold;
        mpfr::sech
    }
    math_op1! {
        /// Computes the hyperbolic cosecant, rounding to the nearest.
        fn csch();
        /// Computes the hyperbolic cosecant, applying the specified
        /// rounding method.
        fn csch_round;
        /// Hold a computation of the hyperbolic cosecant.
        fn csch_hold -> CschHold;
        mpfr::csch
    }
    math_op1! {
        /// Computes the hyperbolic cotangent, rounding to the nearest.
        fn coth();
        /// Computes the hyperbolic cotangent, applying the specified
        /// rounding method.
        fn coth_round;
        /// Hold a computation of the hyperbolic cotangent.
        fn coth_hold -> CothHold;
        mpfr::coth
    }
    math_op1! {
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        fn acosh();
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        fn acosh_round;
        /// Hold a computation of the inverse hyperbolic cosine
        fn acosh_hold -> AcoshHold;
        mpfr::acosh
    }
    math_op1! {
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        fn asinh();
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        fn asinh_round;
        /// Hold a computation of the inverse hyperbolic sine.
        fn asinh_hold -> AsinhHold;
        mpfr::asinh
    }
    math_op1! {
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        fn atanh();
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        fn atanh_round;
        /// Hold a computation of the inverse hyperbolic tangent.
        fn atanh_hold -> AtanhHold;
        mpfr::atanh
    }

    /// Sets `self` to the factorial of `u`, rounding to the nearest.
    pub fn assign_factorial_u(&mut self, u: u32) {
        self.assign_factorial_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the factorial of `u`, applying the specified
    /// rounding method.
    pub fn assign_factorial_u_round(
        &mut self,
        u: u32,
        round: Round,
    ) -> Ordering {
        let mpfr_ret =
            unsafe { mpfr::fac_ui(self.inner_mut(), u.into(), rraw(round)) };
        mpfr_ret.cmp(&0)
    }

    math_op1! {
        /// Computes the natural logarithm of one plus `self`, rounding to
        /// the nearest.
        fn ln_1p();
        /// Computes the natural logarithm of one plus `self`, applying
        /// the specified rounding method.
        fn ln_1p_round;
        /// Hold a computation of the natural logorithm of one plus the
        /// value.
        fn ln_1p_hold -> Ln1pHold;
        mpfr::log1p
    }
    math_op1! {
        /// Subtracts one from the exponential of `self`, rounding to the
        /// nearest.
        fn exp_m1();
        /// Subtracts one from the exponential of `self`, applying the
        /// specified rounding method.
        fn exp_m1_round;
        /// Hold a computation of one less than the exponential of the
        /// value.
        fn exp_m1_hold -> ExpM1Hold;
        mpfr::expm1
    }
    math_op1! {
        /// Computes the exponential integral, rounding to the nearest.
        fn eint();
        /// Computes the exponential integral, applying the specified
        /// rounding method.
        fn eint_round;
        /// Hold a computation of the exponential integral.
        fn eint_hold -> EintHold;
        mpfr::eint
    }
    math_op1! {
        /// Computes the real part of the dilogarithm of `self`, rounding
        /// to the nearest.
        fn li2();
        /// Computes the real part of the dilogarithm of `self`, applying
        /// the specified rounding method.
        fn li2_round;
        /// Hold a computation of the real part of the dilogarithm of the
        /// value.
        fn li2_hold -> Li2Hold;
        mpfr::li2
    }
    math_op1! {
        /// Computes the value of the Gamma function on `self`, rounding
        /// to the nearest.
        fn gamma();
        /// Computes the value of the Gamma function on `self`, applying
        /// the specified rounding method.
        fn gamma_round;
        /// Hold a computation of the Gamma function on the value.
        fn gamma_hold -> GammaHold;
        mpfr::gamma
    }
    math_op1! {
        /// Computes the logarithm of the Gamma function on `self`,
        /// rounding to the nearest.
        fn ln_gamma();
        /// Computes the logarithm of the Gamma function on `self`,
        /// applying the specified rounding method.
        fn ln_gamma_round;
        /// Hold a computation of the logarithm of the Gamma function on
        /// the value.
        fn ln_gamma_hold -> LnGammaHold;
        mpfr::lngamma
    }

    /// Computes the logarithm of the absolute value of the Gamma
    /// function on `self`, rounding to the nearest.
    ///
    /// Returns `Ordering::Less` if the Gamma function is negative, or
    /// `Ordering::Greater` if the Gamma function is positive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugflo;
    /// use rugflo::{Constant, Float};
    /// use rugint::Assign;
    /// use std::cmp::Ordering;
    /// fn main() {
    ///     let mut f;
    ///     let mut check = Float::new(53);
    ///
    ///     // gamma of 1/2 is sqrt(pi)
    ///     f = Float::from((Constant::Pi, 64));
    ///     f.sqrt().ln();
    ///     let lgamma_1_2 = f;
    ///
    ///     f = Float::from((0.5, 53));
    ///     // gamma of 1/2 is positive
    ///     assert_eq!(f.ln_abs_gamma(), Ordering::Greater);
    ///     // check is correct to 53 significant bits
    ///     check.assign(&lgamma_1_2);
    ///     assert_eq!(f, check);
    ///
    ///     // gamma of -1/2 is -2 * sqrt(pi)
    ///     f = Float::from((Constant::Pi, 64)) * 4;
    ///     f.sqrt().ln();
    ///     let lgamma_neg_1_2 = f;
    ///
    ///     f = Float::from((-0.5, 53));
    ///     // gamma of -1/2 is negative
    ///     assert_eq!(f.ln_abs_gamma(), Ordering::Less);
    ///     // check is correct to 53 significant bits
    ///     check.assign(&lgamma_neg_1_2);
    ///     assert_eq!(f, check);
    /// }
    /// ```
    pub fn ln_abs_gamma(&mut self) -> Ordering {
        self.ln_abs_gamma_round(Round::Nearest).0
    }

    /// Computes the logarithm of the absolute value of the Gamma
    /// function on `self`, applying the specified rounding method.
    ///
    /// The returned tuple contains:
    ///
    /// 1. The logarithm of the absolute value of the Gamma function.
    /// 2. The rounding direction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugflo::{AssignRound, Constant, Float, Round};
    /// use std::cmp::Ordering;
    ///
    /// let mut f: Float;
    /// let mut check = Float::new(53);
    ///
    /// // gamma of -1/2 is -2 * sqrt(pi)
    /// f = Float::from((Constant::Pi, 64)) * 4;
    /// f.sqrt().ln();
    /// let lgamma_neg_1_2 = f;
    ///
    /// f = Float::from((-0.5, 53));
    /// let (sign, dir) = f.ln_abs_gamma_round(Round::Nearest);
    /// // gamma of -1/2 is negative
    /// assert_eq!(sign, Ordering::Less);
    /// // check is correct to 53 significant bits
    /// let check_dir = check.assign_round(&lgamma_neg_1_2, Round::Nearest);
    /// assert_eq!(f, check);
    /// assert_eq!(dir, check_dir);
    /// ```
    pub fn ln_abs_gamma_round(&mut self, round: Round) -> (Ordering, Ordering) {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let mpfr_ret = unsafe {
            mpfr::lgamma(self.inner_mut(), sign_ptr, self.inner(), rraw(round))
        };
        let sign_ord = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        (sign_ord, mpfr_ret.cmp(&0))
    }

    /// Holds the computation of the logarithm of the absolute value of the
    /// Gamma function on `val`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugflo;
    /// use rugflo::{AssignRound, Constant, Float, Round};
    /// use rugint::Assign;
    /// use std::cmp::Ordering;
    /// fn main() {
    ///     let mut f: Float;
    ///     let mut check = Float::new(53);
    ///
    ///     // gamma of -1/2 is -2 * sqrt(pi)
    ///     f = Float::from((Constant::Pi, 64)) * 4;
    ///     f.sqrt().ln();
    ///     let lgamma_neg_1_2 = f;
    ///
    ///     let neg_1_2 = Float::from((-0.5, 53));
    ///     f = Float::new(53);
    ///     let mut sign = Ordering::Equal;
    ///
    ///     // Assign rounds to the nearest
    ///     let hold = neg_1_2.ln_abs_gamma_hold();
    ///     (&mut f, &mut sign).assign(hold);
    ///     // gamma of -1/2 is negative
    ///     assert_eq!(sign, Ordering::Less);
    ///     // check is correct to 53 significant bits
    ///     check.assign(&lgamma_neg_1_2);
    ///     assert_eq!(f, check);
    ///
    ///     // AssignRound returns the rounding direction
    ///     let hold = neg_1_2.ln_abs_gamma_hold();
    ///     let dir = (&mut f, &mut sign).assign_round(hold, Round::Nearest);
    ///     // gamma of -1/2 is negative
    ///     assert_eq!(sign, Ordering::Less);
    ///     // check is correct to 53 significant bits
    ///     let check_dir = check.assign_round(&lgamma_neg_1_2, Round::Nearest);
    ///     assert_eq!(f, check);
    ///     assert_eq!(dir, check_dir);
    /// }
    /// ```
    pub fn ln_abs_gamma_hold(&self) -> LnAbsGammaHold {
        LnAbsGammaHold { hold_self: self }
    }

    math_op1! {
        /// Computes the value of the Digamma function on `self`, rounding
        /// to the nearest.
        fn digamma();
        /// Computes the value of the Digamma function on `self`, applying
        /// the specified rounding method.
        fn digamma_round;
        /// Hold a computation of the Digamma function on the value.
        fn digamma_hold -> DigammaHold;
        mpfr::digamma
    }
    math_op1! {
        /// Computes the value of the Riemann Zeta function on `self`,
        /// rounding to the nearest.
        fn zeta();
        /// Computes the value of the Riemann Zeta function on `self`,
        /// applying the specified rounding method.
        fn zeta_round;
        /// Hold a computation of the Riemann Zeta function on the value.
        fn zeta_hold -> ZetaHold;
        mpfr::zeta
    }

    /// Sets `self` to the value of the Riemann Zeta function on `u`,
    /// rounding to the nearest.
    pub fn assign_zeta_u(&mut self, u: u32) {
        self.assign_zeta_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the value of the Riemann Zeta function on `u`,
    /// applying the specified rounding method.
    pub fn assign_zeta_u_round(&mut self, u: u32, round: Round) -> Ordering {
        let mpfr_ret =
            unsafe { mpfr::zeta_ui(self.inner_mut(), u.into(), rraw(round)) };
        mpfr_ret.cmp(&0)
    }

    math_op1! {
        /// Computes the value of the error function, rounding to the
        /// nearest.
        fn erf();
        /// Computes the value of the error function, applying the
        /// specified rounding method.
        fn erf_round;
        /// Hold a computation of the error function.
        fn erf_hold -> ErfHold;
        mpfr::erf
    }
    math_op1! {
        /// Computes the value of the complementary error function,
        /// rounding to the nearest.
        fn erfc();
        /// Computes the value of the complementary error function,
        /// applying the specified rounding method.
        fn erfc_round;
        /// Hold a computation of the complementary error function.
        fn erfc_hold -> ErfcHold;
        mpfr::erfc
    }
    math_op1! {
        /// Computes the value of the first kind Bessel function of order
        /// 0, rounding to the nearest.
        fn j0();
        /// Computes the value of the first kind Bessel function of order
        /// 0, applying the specified rounding method.
        fn j0_round;
        /// Hold a computation of the first kind Bessel function of order
        /// 0.
        fn j0_hold -> J0Hold;
        mpfr::j0
    }
    math_op1! {
        /// Computes the value of the first kind Bessel function of order
        /// 1, rounding to the nearest.
        fn j1();
        /// Computes the value of the first kind Bessel function of order
        /// 1, applying the specified rounding method.
        fn j1_round;
        /// Hold a computation of the first kind Bessel function of order
        /// 1.
        fn j1_hold -> J1Hold;
        mpfr::j1
    }
    math_op1! {
        /// Computes the value of the first kind Bessel function of order
        /// `n`, rounding to the nearest.
        fn jn(n: i32);
        /// Computes the value of the first kind Bessel function of order
        /// `n`, applying the specified rounding method.
        fn jn_round;
        /// Hold a computation of the first kind Bessel function of order
        /// `n`.
        fn jn_hold -> JnHold;
        xmpfr::jn
    }
    math_op1! {
        /// Computes the value of the second kind Bessel function of order
        /// 0, rounding to the nearest.
        fn y0();
        /// Computes the value of the second kind Bessel function of order
        /// 0, applying the specified rounding method.
        fn y0_round;
        /// Hold a computation of the second kind Bessel function of order
        /// 0.
        fn y0_hold -> Y0Hold;
        mpfr::y0
    }
    math_op1! {
        /// Computes the value of the second kind Bessel function of order
        /// 1, rounding to the nearest.
        fn y1();
        /// Computes the value of the second kind Bessel function of order
        /// 1, applying the specified rounding method.
        fn y1_round;
        /// Hold a computation of the second kind Bessel function of order
        /// 1.
        fn y1_hold -> Y1Hold;
        mpfr::y1
    }
    math_op1! {
        /// Computes the value of the second kind Bessel function of order
        /// `n`, rounding to the nearest.
        fn yn(n: i32);
        /// Computes the value of the second kind Bessel function of order
        /// `n`, applying the specified rounding method.
        fn yn_round;
        /// Hold a computation of the second kind Bessel function of order
        /// `n`.
        fn yn_hold -> YnHold;
        xmpfr::yn
    }
    math_op2! {
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// rounding to the nearest.
        fn agm(other);
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// applying the specified rounding method.
        fn agm_round;
        /// Hold a computation of the arithmetic-geometric mean.
        fn agm_hold -> AgmHold;
        mpfr::agm
    }
    math_op2! {
        /// Computes the Euclidean norm of `self` and `other`, rounding to
        /// the nearest.
        fn hypot(other);
        /// Computes the Euclidean norm of `self` and `other`, applying
        /// the specified rounding method.
        fn hypot_round;
        /// Hold a computation of the Euclidean norm.
        fn hypot_hold -> HypotHold;
        mpfr::hypot
    }
    math_op1! {
        /// Computes the value of the Airy function Ai on `self`, rounding
        /// to the nearest.
        fn ai();
        /// Computes the value of the Airy function Ai on `self`, applying
        /// the specified rounding method.
        fn ai_round;
        /// Hold a computation of the Airy function Ai on the value.
        fn ai_hold -> AiHold;
        mpfr::ai
    }
    math_op1! {
        /// Rounds up to the next higher integer, then rounds to the
        /// nearest. This function performs double rounding.
        fn ceil();
        /// Rounds up to the next higher integer, then applies the
        /// specified rounding method. This function performs double
        /// rounding.
        fn ceil_round;
        /// Hold a rounding to the next higher integer with double
        /// rounding.
        fn ceil_hold -> CeilHold;
        mpfr::rint_ceil
    }
    math_op1! {
        /// Rounds down to the next lower integer, then rounds to the
        /// nearest. This function performs double rounding.
        fn floor();
        /// Rounds down to the next lower integer, then applies the
        /// specified rounding method. This function performs double
        /// rounding.
        fn floor_round;
        /// Hold a rounding to the next lower integer with double
        /// rounding.
        fn floor_hold -> FloorHold;
        mpfr::rint_floor
    }
    math_op1! {
        /// Rounds to the nearest integer, rounding half-way cases away
        /// from zero, then rounds to the nearest representable value.
        /// This function performs double rounding.
        fn round();
        /// Rounds to the nearest integer, rounding half-way cases away
        /// from zero, then applies the specified rounding method to get a
        /// representable value. This function performs double rounding.
        fn round_round;
        /// Hold a rounding to the nearest integer, rounding half-way
        /// cases away from zero, with double rounding.
        fn round_hold -> RoundHold;
        mpfr::rint_round
    }
    math_op1! {
        /// Rounds to the next integer towards zero, then rounds to the
        /// nearest. This function performs double rounding.
        fn trunc();
        /// Rounds to the next integer towards zero, then applies the
        /// specified rounding method. This function performs double
        /// rounding.
        fn trunc_round;
        /// Hold a rounding to the next integer towards zero with double
        /// roundign.
        fn trunc_hold -> TruncHold;
        mpfr::rint_trunc
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
    pub fn assign_random_bits_round<R: Rng>(
        &mut self,
        rng: &mut R,
        round: Round,
    ) -> Ordering {
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
                mpfr::set_zero(self.inner_mut(), 0);
            }
            return Ordering::Equal;
        }
        let zero_bits = (lead_zeros % limb_bits) as c_uint;
        let err = unsafe {
            mpfr::set_exp(self.inner_mut(), -(lead_zeros as mpfr::exp_t))
        };
        if err != 0 {
            // This is extremely unlikely, we can be inefficient.
            // Firs set MSB, then subtract by 0.5
            let high_one: gmp::limb_t = 1 << (limb_bits - 1);
            limbs[total_limbs - 1] |= high_one;
            let mpfr_ret = unsafe {
                mpfr::set_exp(self.inner_mut(), 0);
                mpfr::sub_d(self.inner_mut(), self.inner(), 0.5, rraw(round))
            };
            return mpfr_ret.cmp(&0);
        }
        if zero_bits > 0 {
            let ptr_offset = zero_limbs as isize;
            unsafe {
                gmp::mpn_lshift(
                    self.inner.d.offset(ptr_offset),
                    self.inner.d,
                    (total_limbs - zero_limbs) as gmp::size_t,
                    zero_bits,
                );
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
    ///     assert_ne!(dir, Ordering::Equal);
    ///     // The significand is either 0b10 or 0b11
    ///     //           10          11
    ///     assert!(f == 1.0 || f == 0.75 ||
    ///             f == 0.5 || f == 0.375 ||
    ///             f == 0.25 || f <= 0.1875);
    ///     // If the result is 1.0, rounding was up.
    ///     assert!(f != 1.0 || dir == Ordering::Greater);
    /// }
    /// ```
    pub fn assign_random_cont_round<R: Rng>(
        &mut self,
        rng: &mut R,
        round: Round,
    ) -> Ordering {
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
            mpfr::nextabove(self.inner_mut());
        }
        Ordering::Greater
    }

    #[cfg(feature = "random")]
    fn random_cont_first_limb<R: Rng>(
        &mut self,
        bits: usize,
        rng: &mut R,
        round: Round,
    ) -> Option<Ordering> {
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
                    mpfr::set_zero(self.inner_mut(), 0);
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
                    mpfr::nextabove(self.inner_mut());
                }
                return Some(Ordering::Greater);
            }
            exp -= zeros;
            if val != 0 {
                unsafe {
                    mpfr::set_exp(self.inner_mut(), exp.into());
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
}

enum PossibleFromStr<'a> {
    Owned(String),
    Borrowed(&'a str),
    Special(Special),
}

// If will_use_returned is false, do not allocate as the result will
// be discarded anyway.
fn check_str_radix(
    src: &str,
    radix: i32,
    will_use_returned: bool,
) -> Result<PossibleFromStr, ParseFloatError> {
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

impl<T> From<(T, u32)> for Float
where
    Float: FromRound<T, u32, Round = Round>,
{
    fn from((t, prec): (T, u32)) -> Float {
        Float::from_round(t, prec, Round::Nearest).0
    }
}

impl<T> FromRound<T, u32> for Float
where
    Float: AssignRound<T,
                       Round = Round,
                       Ordering = Ordering>,
{
    type Round = Round;
    type Ordering = Ordering;
    fn from_round(t: T, prec: u32, round: Round) -> (Float, Ordering) {
        let mut ret = Float::new(prec);
        let ord = ret.assign_round(t, round);
        (ret, ord)
    }
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

impl<T> Assign<T> for Float
where
    Float: AssignRound<T,
                       Round = Round,
                       Ordering = Ordering>,
{
    fn assign(&mut self, other: T) {
        self.assign_round(other, Round::Nearest);
    }
}

impl AssignRound<Constant> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, other: Constant, round: Round) -> Ordering {
        let mpfr_ret = unsafe {
            match other {
                Constant::Log2 => {
                    mpfr::const_log2(self.inner_mut(), rraw(round))
                }
                Constant::Pi => mpfr::const_pi(self.inner_mut(), rraw(round)),
                Constant::Euler => {
                    mpfr::const_euler(self.inner_mut(), rraw(round))
                }
                Constant::Catalan => {
                    mpfr::const_catalan(self.inner_mut(), rraw(round))
                }
            }
        };
        mpfr_ret.cmp(&0)
    }
}

impl AssignRound<Special> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, other: Special, _round: Round) -> Ordering {
        unsafe {
            match other {
                Special::Zero => mpfr::set_zero(self.inner_mut(), 0),
                Special::MinusZero => mpfr::set_zero(self.inner_mut(), -1),
                Special::Infinity => mpfr::set_inf(self.inner_mut(), 0),
                Special::MinusInfinity => mpfr::set_inf(self.inner_mut(), -1),
                Special::Nan => mpfr::set_nan(self.inner_mut()),
            };
        }
        Ordering::Equal
    }
}

macro_rules! assign {
    { $T:ty, $func:path } => {
        impl<'a> AssignRound<&'a $T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(
                &mut self,
                other: &'a $T,
                round: Round
            ) -> Ordering {
                let mpfr_ret = unsafe {
                    $func(self.inner_mut(), other.inner(), rraw(round))
                };
                mpfr_ret.cmp(&0)
            }
        }

        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(&mut self, other: $T, round: Round) -> Ordering {
                self.assign_round(&other, round)
            }
        }
    };
}

assign! { Float, mpfr::set }
assign! { Integer, mpfr::set_z }
assign! { Rational, mpfr::set_q }

hold_math_op1! { struct SquareHold {}; mpfr::sqr }
hold_math_op1! { struct SqrtHold {}; mpfr::sqrt }
hold_math_op1! { struct RecipSqrtHold {}; mpfr::rec_sqrt }
hold_math_op1! { struct CbrtHold {}; mpfr::cbrt }
hold_math_op1! { struct RootHold { k: u32 }; mpfr::root }
hold_math_op1! { struct AbsHold {}; mpfr::abs }
hold_math_op1! { struct RecipHold {}; xmpfr::recip }
hold_math_op2! { struct AbsDiffHold { other }; mpfr::dim }
hold_math_op1! { struct LnHold {}; mpfr::log }
hold_math_op1! { struct Log2Hold {}; mpfr::log2 }
hold_math_op1! { struct Log10Hold {}; mpfr::log10 }
hold_math_op1! { struct ExpHold {}; mpfr::exp }
hold_math_op1! { struct Exp2Hold {}; mpfr::exp2 }
hold_math_op1! { struct Exp10Hold {}; mpfr::exp10 }
hold_math_op1! { struct SinHold {}; mpfr::sin }
hold_math_op1! { struct CosHold {}; mpfr::cos }
hold_math_op1! { struct TanHold {}; mpfr::tan }
hold_math_op1_2! { struct SinCosHold {}; mpfr::sin_cos }
hold_math_op1! { struct SecHold {}; mpfr::sec }
hold_math_op1! { struct CscHold {}; mpfr::csc }
hold_math_op1! { struct CotHold {}; mpfr::cot }
hold_math_op1! { struct AcosHold {}; mpfr::acos }
hold_math_op1! { struct AsinHold {}; mpfr::asin }
hold_math_op1! { struct AtanHold {}; mpfr::atan }
hold_math_op2! { struct Atan2Hold { other }; mpfr::atan2 }
hold_math_op1! { struct CoshHold {}; mpfr::cosh }
hold_math_op1! { struct SinhHold {}; mpfr::sinh }
hold_math_op1! { struct TanhHold {}; mpfr::tanh }
hold_math_op1_2! { struct SinhCoshHold {}; mpfr::sinh_cosh }
hold_math_op1! { struct SechHold {}; mpfr::sech }
hold_math_op1! { struct CschHold {}; mpfr::csch }
hold_math_op1! { struct CothHold {}; mpfr::coth }
hold_math_op1! { struct AcoshHold {}; mpfr::acosh }
hold_math_op1! { struct AsinhHold {}; mpfr::asinh }
hold_math_op1! { struct AtanhHold {}; mpfr::atanh }
hold_math_op1! { struct Ln1pHold {}; mpfr::log1p }
hold_math_op1! { struct ExpM1Hold {}; mpfr::expm1 }
hold_math_op1! { struct EintHold {}; mpfr::eint }
hold_math_op1! { struct Li2Hold {}; mpfr::li2 }
hold_math_op1! { struct GammaHold {}; mpfr::gamma }
hold_math_op1! { struct LnGammaHold {}; mpfr::lngamma }

pub struct LnAbsGammaHold<'a> {
    hold_self: &'a Float,
}

impl<'a> Assign<LnAbsGammaHold<'a>> for (&'a mut Float, &'a mut Ordering) {
    fn assign(&mut self, src: LnAbsGammaHold<'a>) {
        self.assign_round(src, Round::Nearest);
    }
}

impl<'a> AssignRound<LnAbsGammaHold<'a>> for (&'a mut Float, &'a mut Ordering) {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(
        &mut self,
        src: LnAbsGammaHold<'a>,
        round: Round,
    ) -> Ordering {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let mpfr_ret = unsafe {
            mpfr::lgamma(
                self.0.inner_mut(),
                sign_ptr,
                src.hold_self.inner(),
                rraw(round),
            )
        };
        *self.1 = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        mpfr_ret.cmp(&0)
    }
}

hold_math_op1! { struct DigammaHold {}; mpfr::digamma }
hold_math_op1! { struct ZetaHold {}; mpfr::zeta }
hold_math_op1! { struct ErfHold {}; mpfr::erf }
hold_math_op1! { struct ErfcHold {}; mpfr::erfc }
hold_math_op1! { struct J0Hold {}; mpfr::j0 }
hold_math_op1! { struct J1Hold {}; mpfr::j1 }
hold_math_op1! { struct JnHold { n: i32 }; xmpfr::jn }
hold_math_op1! { struct Y0Hold {}; mpfr::y0 }
hold_math_op1! { struct Y1Hold {}; mpfr::y1 }
hold_math_op1! { struct YnHold { n: i32 }; xmpfr::yn }
hold_math_op2! { struct AgmHold { other }; mpfr::agm }
hold_math_op2! { struct HypotHold { other }; mpfr::hypot }
hold_math_op1! { struct AiHold {}; mpfr::ai }
hold_math_op1! { struct CeilHold {}; mpfr::rint_ceil }
hold_math_op1! { struct FloorHold {}; mpfr::rint_floor }
hold_math_op1! { struct RoundHold {}; mpfr::rint_round }
hold_math_op1! { struct TruncHold {}; mpfr::rint_trunc }

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
            mpfr::neg(self.inner_mut(), self.inner(), rraw(Round::Nearest));
        }
    }
}

impl<'a> Neg for &'a Float {
    type Output = NegHold<'a>;
    fn neg(self) -> NegHold<'a> {
        NegHold { val: self }
    }
}

/// Holds a negation.
pub struct NegHold<'a> {
    val: &'a Float,
}

impl<'a> AssignRound<NegHold<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: NegHold<'a>, round: Round) -> Ordering {
        let mpfr_ret = unsafe {
            mpfr::neg(self.inner_mut(), src.val.inner(), rraw(round))
        };
        mpfr_ret.cmp(&0)
    }
}

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        impl<'a> $Imp<&'a $T> for Float {
            type Output = Float;
            fn $method(self, rhs: &'a $T) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl<'a> $ImpRound<&'a $T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                mut self,
                rhs: &'a $T,
                round: Round,
            ) -> (Float, Ordering) {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw(round),
                    )
                };
                (self, mpfr_ret.cmp(&0))
            }
        }

        impl $Imp<$T> for Float {
            type Output = Float;
            fn $method(self, rhs: $T) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(self, rhs: $T, round: Round) -> (Float, Ordering) {
                self.$method_round(&rhs, round)
            }
        }

        impl<'a> $Imp<&'a $T> for &'a Float {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: OwnBorrow::Borrow(rhs),
                }
            }
        }

        impl<'a> $ImpAssign<&'a $T> for Float {
            fn $method_assign(&mut self, rhs: &'a $T) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw(Round::Nearest),
                    );
                }
            }
        }

        impl $ImpAssign<$T> for Float {
            fn $method_assign(&mut self, rhs: $T) {
                self.$method_assign(&rhs);
            }
        }

        pub struct $Hold<'a> {
            lhs: &'a Float,
            rhs: OwnBorrow<'a, $T>,
        }

        impl<'a> AssignRound<$Hold<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(&mut self, src: $Hold, round: Round) -> Ordering {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
            }
        }
    };
}

macro_rules! arith_commut_float {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Float,
            $func,
            $Hold
        }

        impl<'a> $Imp<Float> for &'a Float {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl<'a> $ImpRound<Float> for &'a Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                rhs.$method_round(self, round)
            }
        }
    }
}

macro_rules! arith_noncommut_float {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Float,
            $func,
            $Hold
        }

        impl<'a> $Imp<Float> for &'a Float {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl<'a> $ImpRound<Float> for &'a Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                mut rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                let mpfr_ret = unsafe {
                    $func(
                        rhs.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw(round),
                    )
                };
                (rhs, mpfr_ret.cmp(&0))
            }
        }

        impl<'a> $ImpFromAssign<&'a Float> for Float {
            fn $method_from_assign(&mut self, lhs: &Float) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
                        rraw(Round::Nearest),
                    );
                }
            }
        }

        impl $ImpFromAssign for Float {
            fn $method_from_assign(&mut self, lhs: Float) {
                self.$method_from_assign(&lhs);
            }
        }
    }
}

macro_rules! arith_forward {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<$T> for &'a Float {
            type Output = $Hold<'a>;
            fn $method(self, rhs: $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: OwnBorrow::Own(rhs),
                }
            }
        }
    };
}

macro_rules! arith_commut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<Float> for &'a $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl<'a> $ImpRound<Float> for &'a $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                rhs.$method_round(self, round)
            }
        }

        impl $Imp<Float> for $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Float> for &'a $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Float) -> $Hold<'a> {
                rhs.$method(self)
            }
        }

        impl<'a> $Imp<&'a Float> for $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Float) -> $Hold<'a> {
                rhs.$method(self)
            }
        }
    };
}

macro_rules! arith_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $T:ty,
        $func:path,
        $func_from:path,
        $Hold:ident,
        $HoldFrom:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<Float> for &'a $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl<'a> $ImpRound<Float> for &'a $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                mut rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                let mpfr_ret = unsafe {
                    $func_from(
                        rhs.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw(round),
                    )
                };
                (rhs, mpfr_ret.cmp(&0))
            }
        }

        impl $Imp<Float> for $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                (&self).$method_round(rhs, round)
            }
        }

        impl<'a> $Imp<&'a Float> for &'a $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Float) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: OwnBorrow::Borrow(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $Imp<&'a Float> for $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Float) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: OwnBorrow::Own(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $ImpFromAssign<&'a $T> for Float {
            fn $method_from_assign(&mut self, lhs: &'a $T) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
                        rraw(Round::Nearest),
                    );
                }
            }
        }

        impl $ImpFromAssign<$T> for Float {
            fn $method_from_assign(&mut self, lhs: $T) {
                self.$method_from_assign(&lhs);
            }
        }

        pub struct $HoldFrom<'a> {
            lhs: OwnBorrow<'a, $T>,
            rhs: &'a Float,
        }

        impl<'a> AssignRound<$HoldFrom<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(
                &mut self,
                src: $HoldFrom,
                round: Round,
            ) -> Ordering {
                let mpfr_ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
            }
        }
    };
}

arith_commut_float! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    mpfr::add,
    AddHold
}
arith_noncommut_float! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    mpfr::sub,
    SubHold
}
arith_commut_float! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    mpfr::mul,
    MulHold
}
arith_noncommut_float! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    mpfr::div,
    DivHold
}
arith_noncommut_float! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    PowFromAssign pow_from_assign,
    mpfr::pow,
    PowHold
}

arith_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    Integer,
    mpfr::add_z,
    AddHoldInteger
}
arith_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    Integer,
    mpfr::sub_z,
    mpfr::z_sub,
    SubHoldInteger,
    SubFromHoldInteger
}
arith_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    Integer,
    mpfr::mul_z,
    MulHoldInteger
}
arith_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    Integer,
    mpfr::div_z,
    xmpfr::z_div,
    DivHoldInteger,
    DivFromHoldInteger
}
arith_forward! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    Integer,
    mpfr::pow_z,
    PowHoldInteger
}

arith_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    Rational,
    mpfr::add_q,
    AddHoldRational
}
arith_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    Rational,
    mpfr::sub_q,
    xmpfr::q_sub,
    SubHoldRational,
    SubFromHoldRational
}
arith_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    Rational,
    mpfr::mul_q,
    MulHoldRational
}
arith_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    Rational,
    mpfr::div_q,
    xmpfr::q_div,
    DivHoldRational,
    DivFromHoldRational
}

macro_rules! arith_prim {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    }=> {
        impl $Imp<$T> for Float {
            type Output = Float;
            fn $method(self, rhs: $T) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                mut self,
                rhs: $T,
                round: Round,
            ) -> (Float, Ordering) {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        rraw(round),
                    )
                };
                (self, mpfr_ret.cmp(&0))
            }
        }

        impl<'a> $Imp<$T> for &'a Float {
            type Output = $Hold<'a>;
            fn $method(self, rhs: $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpAssign<$T> for Float {
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        rraw(Round::Nearest),
                    );
                }
            }
        }

        pub struct $Hold<'a> {
            lhs: &'a Float,
            rhs: $T,
        }

        impl<'a> AssignRound<$Hold<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(&mut self, src: $Hold, round: Round) -> Ordering {
                let mpfr_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.into(),
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
            }
        }
    };
}

macro_rules! arith_prim_commut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    }=> {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Float> for $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Float> for $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Float) -> $Hold<'a> {
                rhs.$method(self)
            }
        }
    };
}

macro_rules! arith_prim_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $T:ty,
        $func:path,
        $func_from:path,
        $Hold:ident,
        $HoldFrom:ident
    } => {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Float> for $T {
            type Output = Float;
            fn $method(self, rhs: Float) -> Float {
                self.$method_round(rhs, Round::Nearest).0
            }
        }

        impl $ImpRound<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            type Output = Float;
            fn $method_round(
                self,
                mut rhs: Float,
                round: Round,
            ) -> (Float, Ordering) {
                let mpfr_ret = unsafe {
                    $func_from(
                        rhs.inner_mut(),
                        self.into(),
                        rhs.inner(),
                        rraw(round),
                    )
                };
                (rhs, mpfr_ret.cmp(&0))
            }
        }

        impl<'a> $Imp<&'a Float> for $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Float) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpFromAssign<$T> for Float {
            fn $method_from_assign(&mut self, lhs: $T) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.into(),
                        self.inner(),
                        rraw(Round::Nearest),
                    );
                }
            }
        }

        /// Holds an operation.
        pub struct $HoldFrom<'a> {
            lhs: $T,
            rhs: &'a Float,
        }

        impl<'a> AssignRound<$HoldFrom<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(
                &mut self,
                src: $HoldFrom,
                round: Round,
            ) -> Ordering {
                let mpfr_ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.into(),
                        src.rhs.inner(),
                        rraw(round),
                    )
                };
                mpfr_ret.cmp(&0)
            }
        }
    };
}

macro_rules! conv_ops {
    {
        ($T:ty, $set:path),
        ($AddHold:ident $add:path,
         $SubHold:ident $sub:path,
         $SubFromHold:ident $sub_from:path),
        ($MulHold:ident $mul:path,
         $DivHold:ident $div: path,
         $DivFromHold:ident $div_from:path)
    } => {
        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            fn assign_round(&mut self, val: $T, round: Round) -> Ordering {
                let mpfr_ret = unsafe {
                    $set(self.inner_mut(), val.into(), rraw(round))
                };
                mpfr_ret.cmp(&0)
            }
        }

        arith_prim_commut! {
            Add add,
            AddRound add_round,
            AddAssign add_assign,
            $T,
            $add,
            $AddHold
        }
        arith_prim_noncommut! {
            Sub sub,
            SubRound sub_round,
            SubAssign sub_assign,
            SubFromAssign sub_from_assign,
            $T,
            $sub,
            $sub_from,
            $SubHold,
            $SubFromHold
        }
        arith_prim_commut! {
            Mul mul,
            MulRound mul_round,
            MulAssign mul_assign,
            $T,
            $mul,
            $MulHold
        }
        arith_prim_noncommut! {
            Div div,
            DivRound div_round,
            DivAssign div_assign,
            DivFromAssign div_from_assign,
            $T,
            $div,
            $div_from,
            $DivHold,
            $DivFromHold
        }
    }
}

conv_ops! {
    (i32, mpfr::set_si),
    (AddHoldI32 mpfr::add_si,
     SubHoldI32 mpfr::sub_si,
     SubFromHoldI32 mpfr::si_sub),
    (MulHoldI32 mpfr::mul_si,
     DivHoldI32 mpfr::div_si,
     DivFromHoldI32 mpfr::si_div)
}

impl AssignRound<i64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, other: i64, round: Round) -> Ordering {
        let mpfr_ret =
            unsafe { xmpfr::set_i64(self.inner_mut(), other, rraw(round)) };
        mpfr_ret.cmp(&0)
    }
}

conv_ops! {
    (u32, mpfr::set_ui),
    (AddHoldU32 mpfr::add_ui,
     SubHoldU32 mpfr::sub_ui,
     SubFromHoldU32 mpfr::ui_sub),
    (MulHoldU32 mpfr::mul_ui,
     DivHoldU32 mpfr::div_ui,
     DivFromHoldU32 mpfr::ui_div)
}

impl AssignRound<u64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, other: u64, round: Round) -> Ordering {
        let mpfr_ret =
            unsafe { xmpfr::set_u64(self.inner_mut(), other, rraw(round)) };
        mpfr_ret.cmp(&0)
    }
}

conv_ops! {
    (f32, xmpfr::set_single),
    (AddHoldF32 xmpfr::add_single,
     SubHoldF32 xmpfr::sub_single,
     SubFromHoldF32 xmpfr::single_sub),
    (MulHoldF32 xmpfr::mul_single,
     DivHoldF32 xmpfr::div_single,
     DivFromHoldF32 xmpfr::single_div)
}
conv_ops! {
    (f64, mpfr::set_d),
    (AddHoldF64 mpfr::add_d,
     SubHoldF64 mpfr::sub_d,
     SubFromHoldF64 mpfr::d_sub),
    (MulHoldF64 mpfr::mul_d,
     DivHoldF64 mpfr::div_d,
     DivFromHoldF64 mpfr::d_div)
}

arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    u32,
    mpfr::mul_2ui,
    ShlHoldU32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    u32,
    mpfr::div_2ui,
    ShrHoldU32
}
arith_prim_noncommut!{
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    PowFromAssign pow_from_assign,
    u32,
    mpfr::pow_ui,
    mpfr::ui_pow,
    PowHoldU32,
    PowFromHoldU32
}
arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    i32,
    mpfr::mul_2si,
    ShlHoldI32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    i32,
    mpfr::div_2si,
    ShrHoldI32
}
arith_prim!{
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    i32,
    mpfr::pow_si,
    PowHoldI32
}

impl PartialEq for Float {
    fn eq(&self, other: &Float) -> bool {
        unsafe { mpfr::equal_p(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Float {
    /// Returns the ordering of `self` and `other`,
    /// or `None` if one (or both) of them is a NaN.
    fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(mpfr::cmp(self.inner(), other.inner()).cmp(&0)),
                _ => None,
            }
        }
    }

    fn lt(&self, other: &Float) -> bool {
        unsafe { mpfr::less_p(self.inner(), other.inner()) != 0 }
    }

    fn le(&self, other: &Float) -> bool {
        unsafe { mpfr::lessequal_p(self.inner(), other.inner()) != 0 }
    }

    fn gt(&self, other: &Float) -> bool {
        unsafe { mpfr::greater_p(self.inner(), other.inner()) != 0 }
    }

    fn ge(&self, other: &Float) -> bool {
        unsafe { mpfr::greaterequal_p(self.inner(), other.inner()) != 0 }
    }
}

macro_rules! cmp {
    { $T:ty, $eval:expr } => {
        impl PartialEq<$T> for Float {
            fn eq(&self, other: &$T) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Float {
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                if self.is_nan() {
                    return None;
                }
                Some($eval(self.inner(), other).cmp(&0))
            }
        }

        impl PartialEq<Float> for $T {
            fn eq(&self, other: &Float) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<Float> for $T {
            fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    }
}

cmp! { Integer, |f, t: &Integer| unsafe { mpfr::cmp_z(f, t.inner()) } }
cmp! { Rational, |f, t: &Rational| unsafe { mpfr::cmp_q(f, t.inner()) } }
cmp! { u32, |f, t: &u32| unsafe { mpfr::cmp_ui(f, (*t).into()) } }
cmp! { i32, |f, t: &i32| unsafe { mpfr::cmp_si(f, (*t).into()) } }
cmp! { f64, |f, t: &f64| unsafe { mpfr::cmp_d(f, *t) } }
cmp! { f32, |f, t: &f32| unsafe { mpfr::cmp_d(f, *t as f64) } }

fn make_string(
    f: &Float,
    radix: i32,
    precision: Option<usize>,
    round: Round,
    to_upper: bool,
) -> String {
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
        s = mpfr::get_str(
            ptr::null_mut(),
            &mut exp,
            radix.into(),
            digits,
            f.inner(),
            rraw(round),
        );
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
    buf.push(
        if radix <= 10 {
            char_to_upper_if('e', to_upper)
        } else {
            '@'
        }
    );
    let exp = exp.checked_sub(1).expect("overflow");
    let _ = write!(buf, "{}", exp);
    buf
}

fn fmt_radix(
    flt: &Float,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) -> fmt::Result {
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

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Float {
    type Output = mpfr_t;
    fn inner(&self) -> &mpfr_t {
        &self.inner
    }
}

impl InnerMut for Float {
    unsafe fn inner_mut(&mut self) -> &mut mpfr_t {
        &mut self.inner
    }
}

impl Inner for Integer {
    type Output = gmp::mpz_t;
    fn inner(&self) -> &gmp::mpz_t {
        let ptr = self as *const _ as *const gmp::mpz_t;
        unsafe { &*ptr }
    }
}

impl InnerMut for Integer {
    unsafe fn inner_mut(&mut self) -> &mut gmp::mpz_t {
        let ptr = self as *mut _ as *mut gmp::mpz_t;
        &mut *ptr
    }
}

impl Inner for Rational {
    type Output = gmp::mpq_t;
    fn inner(&self) -> &gmp::mpq_t {
        let ptr = self as *const _ as *const gmp::mpq_t;
        unsafe { &*ptr }
    }
}

enum OwnBorrow<'a, T>
where
    T: 'a,
{
    Own(T),
    Borrow(&'a T),
}

impl<'a, T> Inner for OwnBorrow<'a, T>
where
    T: Inner,
{
    type Output = <T as Inner>::Output;
    fn inner(&self) -> &Self::Output {
        match *self {
            OwnBorrow::Own(ref o) => o.inner(),
            OwnBorrow::Borrow(b) => b.inner(),
        }
    }
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
    fn check_ref_op() {
        let lhs = Float::from((12.25, 53));
        let rhs = Float::from((-1.375, 53));
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Float::from((-&lhs, 53)), -lhs.clone());
        assert_eq!(Float::from((&lhs + &rhs, 53)), lhs.clone() + &rhs);
        assert_eq!(Float::from((&lhs - &rhs, 53)), lhs.clone() - &rhs);
        assert_eq!(Float::from((&lhs * &rhs, 53)), lhs.clone() * &rhs);
        assert_eq!(Float::from((&lhs / &rhs, 53)), lhs.clone() / &rhs);
        assert_eq!(Float::from(((&lhs).pow(&rhs), 53)), lhs.clone().pow(&rhs));

        assert_eq!(Float::from((&lhs + pu, 53)), lhs.clone() + pu);
        assert_eq!(Float::from((&lhs - pu, 53)), lhs.clone() - pu);
        assert_eq!(Float::from((&lhs * pu, 53)), lhs.clone() * pu);
        assert_eq!(Float::from((&lhs / pu, 53)), lhs.clone() / pu);
        assert_eq!(Float::from((&lhs << pu, 53)), lhs.clone() << pu);
        assert_eq!(Float::from((&lhs >> pu, 53)), lhs.clone() >> pu);
        assert_eq!(Float::from(((&lhs).pow(pu), 53)), lhs.clone().pow(pu));

        assert_eq!(Float::from((pu + &lhs, 53)), pu + lhs.clone());
        assert_eq!(Float::from((pu - &lhs, 53)), pu - lhs.clone());
        assert_eq!(Float::from((pu * &lhs, 53)), pu * lhs.clone());
        assert_eq!(Float::from((pu / &lhs, 53)), pu / lhs.clone());
        assert_eq!(
            Float::from((Pow::pow(pu, &lhs), 53)),
            Pow::pow(pu, lhs.clone())
        );

        assert_eq!(Float::from((&lhs + pi, 53)), lhs.clone() + pi);
        assert_eq!(Float::from((&lhs - pi, 53)), lhs.clone() - pi);
        assert_eq!(Float::from((&lhs * pi, 53)), lhs.clone() * pi);
        assert_eq!(Float::from((&lhs / pi, 53)), lhs.clone() / pi);
        assert_eq!(Float::from((&lhs << pi, 53)), lhs.clone() << pi);
        assert_eq!(Float::from((&lhs >> pi, 53)), lhs.clone() >> pi);
        assert_eq!(Float::from(((&lhs).pow(pi), 53)), lhs.clone().pow(pi));

        assert_eq!(Float::from((pi + &lhs, 53)), pi + lhs.clone());
        assert_eq!(Float::from((pi - &lhs, 53)), pi - lhs.clone());
        assert_eq!(Float::from((pi * &lhs, 53)), pi * lhs.clone());
        assert_eq!(Float::from((pi / &lhs, 53)), pi / lhs.clone());

        assert_eq!(Float::from((&lhs + ps, 53)), lhs.clone() + ps);
        assert_eq!(Float::from((&lhs - ps, 53)), lhs.clone() - ps);
        assert_eq!(Float::from((&lhs * ps, 53)), lhs.clone() * ps);
        assert_eq!(Float::from((&lhs / ps, 53)), lhs.clone() / ps);

        assert_eq!(Float::from((ps + &lhs, 53)), ps + lhs.clone());
        assert_eq!(Float::from((ps - &lhs, 53)), ps - lhs.clone());
        assert_eq!(Float::from((ps * &lhs, 53)), ps * lhs.clone());
        assert_eq!(Float::from((ps / &lhs, 53)), ps / lhs.clone());

        assert_eq!(Float::from((&lhs + pd, 53)), lhs.clone() + pd);
        assert_eq!(Float::from((&lhs - pd, 53)), lhs.clone() - pd);
        assert_eq!(Float::from((&lhs * pd, 53)), lhs.clone() * pd);
        assert_eq!(Float::from((&lhs / pd, 53)), lhs.clone() / pd);

        assert_eq!(Float::from((pd + &lhs, 53)), pd + lhs.clone());
        assert_eq!(Float::from((pd - &lhs, 53)), pd - lhs.clone());
        assert_eq!(Float::from((pd * &lhs, 53)), pd * lhs.clone());
        assert_eq!(Float::from((pd / &lhs, 53)), pd / lhs.clone());
    }

    #[test]
    fn check_arith_others() {
        let work_prec = 20;
        let check_prec = 100;
        let f = [
            Float::from((Special::Zero, work_prec)),
            Float::from((Special::MinusZero, work_prec)),
            Float::from((Special::Infinity, work_prec)),
            Float::from((Special::MinusInfinity, work_prec)),
            Float::from((Special::Nan, work_prec)),
            Float::from((1, work_prec)),
            Float::from((-1, work_prec)),
            Float::from((999999e100, work_prec)),
            Float::from((999999e-100, work_prec)),
            Float::from((-999999e100, work_prec)),
            Float::from((-999999e-100, work_prec)),
        ];
        let z = [
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        let q = [
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];
        let u = [0, 1, 1000, u32::MAX];
        let s = [i32::MIN, -1000, -1, 0, 1, 1000, i32::MAX];
        let double = [
            f64::INFINITY,
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
            12.0e43,
        ];
        let single = [
            f32::INFINITY,
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
            12.0e30,
        ];
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
        assert!(
            Float::from_str_radix(huge_hex, 16, 53)
                .unwrap()
                .is_infinite()
        );

        let bad_strings = [
            ("inf", 16),
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
            ("9e0", 9),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Float::valid_str_radix(s, radix).is_err());
        }
        let good_strings = [
            ("INF", 10, f64::INFINITY),
            ("-@iNf@", 16, f64::NEG_INFINITY),
            ("+0e99", 2, 0.0),
            ("-9.9e1", 10, -99.0),
            ("-.99e+2", 10, -99.0),
            ("+99.e+0", 10, 99.0),
            ("-99@-1", 10, -9.9f64),
            ("-abc.def@3", 16, -0xabcdef as f64),
            ("1e1023", 2, 2.0f64.powi(1023)),
        ];
        for &(s, radix, f) in good_strings.into_iter() {
            assert_eq!(Float::from_str_radix(s, radix, 53).unwrap(), f);
        }
    }

    #[test]
    fn check_formatting() {
        let mut f = Float::from((Special::Zero, 53));
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "0.0");
        assert_eq!(format!("{:+?}", f), "+0.0");
        f.assign(Special::MinusZero);
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "-0.0");
        assert_eq!(format!("{:+?}", f), "-0.0");
        f.assign(-27);
        assert_eq!(format!("{:.2}", f), "-2.7e1");
        assert_eq!(format!("{:.4?}", f), "-2.700e1");
        assert_eq!(format!("{:.4e}", f), "-2.700e1");
        assert_eq!(format!("{:.4E}", f), "-2.700E1");
        assert_eq!(format!("{:.8b}", f), "-1.1011000e4");
        assert_eq!(format!("{:.3b}", f), "-1.11e4");
        assert_eq!(format!("{:#.8b}", f), "-0b1.1011000e4");
        assert_eq!(format!("{:.2o}", f), "-3.3e1");
        assert_eq!(format!("{:#.2o}", f), "-0o3.3e1");
        assert_eq!(format!("{:.2x}", f), "-1.b@1");
        assert_eq!(format!("{:.2X}", f), "-1.B@1");
        assert_eq!(format!("{:12.1x}", f), "      -1.b@1");
        assert_eq!(format!("{:012.3X}", f), "-000001.B0@1");
        assert_eq!(format!("{:#012.2x}", f), "-0x00001.b@1");
        assert_eq!(format!("{:#12.2X}", f), "    -0x1.B@1");
    }

    #[test]
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
        assert_eq!(unsafe { mpfr::custom_get_size(64) }, 8);
    }
}
