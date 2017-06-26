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

use {Assign, AssignRound, Float};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use ext::mpc as xmpc;
use float::{self, Constant, ParseFloatError, Round, Special, ValidFloat};
use gmp_mpfr_sys::mpc::{self, mpc_t};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
use ops::{AddAssignRound, AddFrom, AddFromRound, DivAssignRound, DivFrom,
          DivFromRound, MulAssignRound, MulFrom, MulFromRound, NegAssign, Pow,
          PowAssign, PowAssignRound, PowFrom, PowFromRound, SubAssignRound,
          SubFrom, SubFromRound};
#[cfg(feature = "rand")]
use rand::RandState;
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::c_int;
use std::ptr;

/// The `Prec` trait is used to specify the precision of the real and
/// imaginary parts of a [`Complex`](../struct.Complex.html) number.
///
/// This trait is implememented for `u32` and for `(u32, u32)`.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// let c1 = Complex::new(32);
/// assert_eq!(c1.prec(), (32, 32));
/// let c2 = Complex::new((32, 64));
/// assert_eq!(c2.prec(), (32, 64));
/// ```
pub trait Prec {
    /// Returns the precision for the real and imaginary parts.
    fn prec(self) -> (u32, u32);
}

impl Prec for u32 {
    #[inline]
    fn prec(self) -> (u32, u32) {
        (self, self)
    }
}

impl Prec for (u32, u32) {
    #[inline]
    fn prec(self) -> (u32, u32) {
        self
    }
}

type Round2 = (Round, Round);

type Ordering2 = (Ordering, Ordering);

/// A multi-precision complex number with arbitrarily large precision
/// and correct rounding.
///
/// The precision has to be set during construction. The rounding
/// method of the required operations can be specified, and the
/// direction of the rounding is returned.
///
/// There are two versions of most methods:
///
/// 1. The first rounds the returned or stored `Complex` number to the
///    [nearest](float/enum.Round.html#variant.Nearest) representable
///    value.
/// 2. The second applies the specified [rounding
///    methods](float/enum.Round.html) for the real and imaginary
///    parts, and returns the rounding directions for both: *
///    `Ordering::Less` if the returned/stored part is less than the
///    exact result, * `Ordering::Equal` if the returned/stored part
///    is equal to the exact result, * `Ordering::Greater` if the
///    returned/stored part is greater than the exact result,
///
/// # Note on [`Round::AwayFromZero`][away]
///
/// For `Complex` numbers, [`Round::AwayFromZero`][away] is not
/// implemented, and trying to use it will panic.
///
/// # Examples
///
/// ```rust
/// use rug::{Assign, Complex, Float};
/// let c = Complex::with_val(53, (40, 30));
/// assert_eq!(format!("{:.3}", c), "(4.00e1 3.00e1)");
/// let mut f = Float::with_val(53, c.abs_ref());
/// assert_eq!(f, 50);
/// f.assign(c.arg_ref());
/// assert_eq!(f, 0.75_f64.atan());
/// ```
///
/// [away]: float/enum.Round.html#variant.AwayFromZero
pub struct Complex {
    inner: mpc_t,
}

impl Clone for Complex {
    #[inline]
    fn clone(&self) -> Complex {
        let prec = self.prec();
        let mut ret = Complex::new(prec);
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Complex) {
        self.assign(source);
    }
}

impl Drop for Complex {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            mpc::clear(self.inner_mut());
        }
    }
}

macro_rules! math_op1_complex {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        math_op1_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $(#[$attr])*
            fn $method($($param: $T),*);
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Ref;
        }
    }
}

macro_rules! ref_math_op1_complex {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        ref_math_op1_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $(#[$attr_ref])*
            struct $Ref { $($param: $T),* }
        }
    }
}

macro_rules! math_op1_2_complex {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        math_op1_2_round! {
            Complex, Round2 => (Ordering2, Ordering2);
            $func, rraw2, rraw2 => ordering4;
            $(#[$attr])*
            fn $method($rop $(, $param: $T)*);
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Ref;
        }
    }
}

macro_rules! ref_math_op1_2_complex {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        ref_math_op1_2_round! {
            Complex, Round2 => (Ordering2, Ordering2);
            $func, rraw2, rraw2 => ordering4;
            $(#[$attr_ref])*
            struct $Ref { $($param: $T),* }
        }
    }
}

impl Complex {
    #[inline]
    fn new_nan<P: Prec>(prec: P) -> Complex {
        let p = prec.prec();
        assert!(
            p.0 >= float::prec_min() && p.0 <= float::prec_max() &&
                p.1 >= float::prec_min() &&
                p.1 <= float::prec_max(),
            "precision out of range"
        );
        unsafe {
            let mut c: Complex = mem::uninitialized();
            mpc::init3(c.inner_mut(), p.0 as mpfr::prec_t, p.1 as mpfr::prec_t);
            c
        }
    }

    /// Create a new complex number with the specified precisions for
    /// the real and imaginary parts and with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c1 = Complex::new(32);
    /// assert_eq!(c1.prec(), (32, 32));
    /// assert_eq!(c1, 0);
    /// let c2 = Complex::new((32, 64));
    /// assert_eq!(c2.prec(), (32, 64));
    /// assert_eq!(c2, 0);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    #[inline]
    pub fn new<P: Prec>(prec: P) -> Complex {
        let mut ret = Complex::new_nan(prec);
        ret.mut_real().assign(Special::Zero);
        ret.mut_imag().assign(Special::Zero);
        ret
    }

    /// Create a new complex number with the specified precision and
    /// with the given value, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c1 = Complex::with_val(53, (1.3f64, -12));
    /// assert_eq!(c1.prec(), (53, 53));
    /// assert_eq!(c1, (1.3f64, -12));
    /// let c2 = Complex::with_val(53, 42.0);
    /// assert_eq!(c2.prec(), (53, 53));
    /// assert_eq!(c2, 42);
    /// assert_eq!(c2, (42, 0));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn with_val<P: Prec, T>(prec: P, val: T) -> Complex
    where
        Complex: Assign<T>,
    {
        let mut ret = Complex::new_nan(prec);
        ret.assign(val);
        ret
    }

    /// Create a new floating-point number with the specified
    /// precision and with the given value, applying the specified
    /// rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let round = (Round::Down, Round::Up);
    /// let (c, dir) = Complex::with_val_round(4, (3.3, 2.3), round);
    /// // 3.3 is rounded down to 3.25, 2.3 is rounded up to 2.5
    /// assert_eq!(c.prec(), (4, 4));
    /// assert_eq!(c, (3.25, 2.5));
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn with_val_round<P: Prec, T>(
        prec: P,
        val: T,
        round: Round2,
    ) -> (Complex, Ordering2)
    where
        Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>,
    {
        let mut ret = Complex::new_nan(prec);
        let ord = ret.assign_round(val, round);
        (ret, ord)
    }

    /// Returns the precision of the real and imaginary parts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let r = Complex::new((24, 53));
    /// assert_eq!(r.prec(), (24, 53));
    /// ```
    #[inline]
    pub fn prec(&self) -> (u32, u32) {
        (self.real().prec(), self.imag().prec())
    }

    /// Sets the precision of the real and imaginary parts, rounding
    /// to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut r = Complex::with_val(6, (4.875, 4.625));
    /// assert_eq!(r, (4.875, 4.625));
    /// r.set_prec(4);
    /// assert_eq!(r, (5.0, 4.5));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    #[inline]
    pub fn set_prec<P: Prec>(&mut self, prec: P) {
        self.set_prec_round(prec, Default::default());
    }

    /// Sets the precision of the real and imaginary parts, applying
    /// the specified rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut r = Complex::with_val(6, (4.875, 4.625));
    /// assert_eq!(r, (4.875, 4.625));
    /// let dir = r.set_prec_round(4, (Round::Down, Round::Up));
    /// assert_eq!(r, (4.5, 5.0));
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    #[inline]
    pub fn set_prec_round<P: Prec>(
        &mut self,
        prec: P,
        round: Round2,
    ) -> Ordering2 {
        let p = prec.prec();
        let (real, imag) = self.as_mut_real_imag();
        (
            real.set_prec_round(p.0, round.0),
            imag.set_prec_round(p.1, round.1),
        )
    }

    /// Parses a `Complex` number with the specified precision,
    /// rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::from_str("(12.5e2 2.5e-1)", 53).unwrap();
    /// assert_eq!(*c.real(), 12.5e2);
    /// assert_eq!(*c.imag(), 2.5e-1);
    /// let bad = Complex::from_str("bad", 53);
    /// assert!(bad.is_err());
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    #[inline]
    pub fn from_str<P: Prec>(
        src: &str,
        prec: P,
    ) -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new_nan(prec);
        val.assign_str(src)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified precision,
    /// applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let round = (Round::Down, Round::Up);
    /// let res = Complex::from_str_round("(14.1 14.2)", 4, round);
    /// let (c, dir) = res.unwrap();
    /// assert_eq!(*c.real(), 14);
    /// assert_eq!(*c.imag(), 15);
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    #[inline]
    pub fn from_str_round<P: Prec>(
        src: &str,
        prec: P,
        round: Round2,
    ) -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new_nan(prec);
        let ord = val.assign_str_round(src, round)?;
        Ok((val, ord))
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::from_str_radix("f.f", 16, 53).unwrap();
    /// assert_eq!(*c.real(), 15.9375);
    /// assert_eq!(*c.imag(), 0);
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn from_str_radix<P: Prec>(
        src: &str,
        radix: i32,
        prec: P,
    ) -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new_nan(prec);
        val.assign_str_radix(src, radix)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let round = (Round::Nearest, Round::Nearest);
    /// let res = Complex::from_str_radix_round("(c.c c.1)", 16, 4, round);
    /// let (c, dir) = res.unwrap();
    /// assert_eq!(*c.real(), 13);
    /// assert_eq!(*c.imag(), 12);
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn from_str_radix_round<P: Prec>(
        src: &str,
        radix: i32,
        prec: P,
        round: Round2,
    ) -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new_nan(prec);
        let ord = val.assign_str_radix_round(src, radix, round)?;
        Ok((val, ord))
    }

    /// Checks if a `Complex` number can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Complex` number. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    ///
    /// let valid1 = Complex::valid_str_radix("(1.2e-1 2.3e+2)", 4);
    /// let c1 = Complex::with_val(53, valid1.unwrap());
    /// assert_eq!(c1, (0.25 * (1.0 + 0.25 * 2.0), 4.0 * (3.0 + 4.0 * 2.0)));
    /// let valid2 = Complex::valid_str_radix("(12 yz)", 36);
    /// let c2 = Complex::with_val(53, valid2.unwrap());
    /// assert_eq!(c2, (2.0 + 36.0 * 1.0, 35.0 + 36.0 * 34.0));
    ///
    /// let invalid = Complex::valid_str_radix("(0, 0)", 3);
    /// let invalid_f = Complex::from_str_radix("(0, 0)", 3, 53);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidComplex, ParseComplexError> {
        use self::ParseComplexError as Error;
        use self::ParseErrorKind as Kind;

        let p = if src.starts_with('(') {
            let space = src.find(' ')
                .ok_or(Error { kind: Kind::MissingSpace })?;
            let real_str = &src[1..space];
            let re = Float::valid_str_radix(real_str, radix)
                .map_err(|e| Error { kind: Kind::InvalidRealFloat(e) })?;
            let rest = &src[space + 1..];
            let close = rest.find(')')
                .ok_or(Error { kind: Kind::MissingClose })?;
            let imag_str = &rest[0..close];
            let im = Float::valid_str_radix(imag_str, radix)
                .map_err(|e| Error { kind: Kind::InvalidImagFloat(e) })?;
            if close != rest.len() - 1 {
                return Err(Error { kind: Kind::CloseNotLast });
            }
            ValidPoss::Complex(re, im)
        } else {
            let re = Float::valid_str_radix(src, radix)
                .map_err(|e| Error { kind: Kind::InvalidFloat(e) })?;
            ValidPoss::Real(re)
        };
        Ok(ValidComplex { poss: p })
    }

    /// Returns a string representation of the value for the specified
    /// `radix` rounding to the nearest.
    ///
    /// The exponent is encoded in decimal. If the number of digits is
    /// not specified, the output string will have enough precision
    /// such that reading it again will give the exact same number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c1 = Complex::with_val(53, 0);
    /// assert_eq!(c1.to_string_radix(10, None), "(0.0 0.0)");
    /// let c2 = Complex::with_val(12, (15, 5));
    /// assert_eq!(c2.to_string_radix(16, None), "(f.000 5.000)");
    /// let c3 = Complex::with_val(53, (10, -4));
    /// assert_eq!(c3.to_string_radix(10, Some(3)), "(1.00e1 -4.00)");
    /// assert_eq!(c3.to_string_radix(5, Some(3)), "(2.00e1 -4.00)");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix(
        &self,
        radix: i32,
        num_digits: Option<usize>,
    ) -> String {
        self.to_string_radix_round(radix, num_digits, Default::default())
    }

    /// Returns a string representation of the value for the specified
    /// `radix` applying the specified rounding method.
    ///
    /// The exponent is encoded in decimal. If the number of digits is
    /// not specified, the output string will have enough precision
    /// such that reading it again will give the exact same number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// let c = Complex::with_val(10, 10.4);
    /// let down = (Round::Down, Round::Down);
    /// let nearest = (Round::Nearest, Round::Nearest);
    /// let up = (Round::Up, Round::Up);
    /// let nd = c.to_string_radix_round(10, None, down);
    /// assert_eq!(nd, "(1.0406e1 0.0)");
    /// let nu = c.to_string_radix_round(10, None, up);
    /// assert_eq!(nu, "(1.0407e1 0.0)");
    /// let sd = c.to_string_radix_round(10, Some(2), down);
    /// assert_eq!(sd, "(1.0e1 0.0)");
    /// let sn = c.to_string_radix_round(10, Some(2), nearest);
    /// assert_eq!(sn, "(1.0e1 0.0)");
    /// let su = c.to_string_radix_round(10, Some(2), up);
    /// assert_eq!(su, "(1.1e1 0.0)");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix_round(
        &self,
        radix: i32,
        num_digits: Option<usize>,
        round: Round2,
    ) -> String {
        let mut buf = String::from("(");
        buf += &self.real()
            .to_string_radix_round(radix, num_digits, round.0);
        buf.push(' ');
        buf += &self.imag()
            .to_string_radix_round(radix, num_digits, round.0);
        buf.push(')');
        buf
    }

    /// Parses a `Complex` number from a string, rounding to the
    /// nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::new(53);
    /// c.assign_str("(12.5e2 2.5e-1)").unwrap();
    /// assert_eq!(*c.real(), 12.5e2);
    /// assert_eq!(*c.imag(), 2.5e-1);
    /// let ret = c.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    #[inline]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseComplexError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Complex` number from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut c = Complex::new((4, 4));
    /// let round = (Round::Down, Round::Up);
    /// let dir = c.assign_str_round("(14.1 14.2)", round).unwrap();
    /// assert_eq!(*c.real(), 14);
    /// assert_eq!(*c.imag(), 15);
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    #[inline]
    pub fn assign_str_round(
        &mut self,
        src: &str,
        round: Round2,
    ) -> Result<Ordering2, ParseComplexError> {
        self.assign_str_radix_round(src, 10, round)
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::new(53);
    /// c.assign_str_radix("f.f", 16).unwrap();
    /// assert_eq!(*c.real(), 15.9375);
    /// assert_eq!(*c.imag(), 0);
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseComplexError> {
        self.assign_str_radix_round(src, radix, Default::default())
            .map(|_| ())
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut c = Complex::new((4, 4));
    /// let round = (Round::Nearest, Round::Nearest);
    /// let dir = c.assign_str_radix_round("(c.c c.1)", 16, round).unwrap();
    /// assert_eq!(*c.real(), 13);
    /// assert_eq!(*c.imag(), 12);
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
    /// ```
    ///
    /// # Errors
    ///
    /// If the string is not correctly formatted, a
    /// [`ParseComplexError`](comples/struct.ParseComplexError.html)
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn assign_str_radix_round(
        &mut self,
        src: &str,
        radix: i32,
        round: Round2,
    ) -> Result<Ordering2, ParseComplexError> {
        Ok(self.assign_round(
            Complex::valid_str_radix(src, radix)?,
            round,
        ))
    }

    /// Borrows the real part as a [`Float`](struct.Float.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (12.5, -20.75));
    /// assert_eq!(*c.real(), 12.5)
    /// ```
    #[inline]
    pub fn real(&self) -> &Float {
        unsafe {
            let ptr = mpc::realref_const(self.inner());
            &*(ptr as *const Float)
        }
    }

    /// Borrows the imaginary part as a [`Float`](struct.Float.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (12.5, -20.75));
    /// assert_eq!(*c.imag(), -20.75)
    #[inline]
    pub fn imag(&self) -> &Float {
        unsafe {
            let ptr = mpc::imagref_const(self.inner());
            &*(ptr as *const Float)
        }
    }

    /// Borrows the real part mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::with_val(53, (12.5, -20.75));
    /// assert_eq!(c, (12.5, -20.75));
    /// *c.mut_real() /= 2;
    /// assert_eq!(c, (6.25, -20.75));
    /// ```
    #[inline]
    pub fn mut_real(&mut self) -> &mut Float {
        unsafe {
            let ptr = mpc::realref(self.inner_mut());
            &mut *(ptr as *mut Float)
        }
    }

    /// Borrows the imaginary part mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::with_val(53, (12.5, -20.75));
    /// assert_eq!(c, (12.5, -20.75));
    /// *c.mut_imag() *= 4;
    /// assert_eq!(c, (12.5, -83));
    /// ```
    #[inline]
    pub fn mut_imag(&mut self) -> &mut Float {
        unsafe {
            let ptr = mpc::imagref(self.inner_mut());
            &mut *(ptr as *mut Float)
        }
    }

    /// Borrows the real and imaginary parts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (12.5, -20.75));
    /// assert_eq!(c, (12.5, -20.75));
    /// let (re, im) = c.as_real_imag();
    /// assert_eq!(*re, 12.5);
    /// assert_eq!(*im, -20.75);
    /// ```
    #[inline]
    pub fn as_real_imag(&self) -> (&Float, &Float) {
        (self.real(), self.imag())
    }

    /// Borrows the real and imaginary parts mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    ///
    /// let mut c = Complex::with_val(53, (12.5, -20.75));
    /// {
    ///     let (real, imag) = c.as_mut_real_imag();
    ///     *real /= 2;
    ///     *imag *= 4;
    ///     // borrow ends here
    /// }
    /// assert_eq!(c, (6.25, -83));
    /// ```
    #[inline]
    pub fn as_mut_real_imag(&mut self) -> (&mut Float, &mut Float) {
        unsafe {
            let real_ptr = mpc::realref(self.inner_mut());
            let imag_ptr = mpc::imagref(self.inner_mut());
            (
                &mut *(real_ptr as *mut Float),
                &mut *(imag_ptr as *mut Float),
            )
        }
    }

    /// Consumes and converts the value into real and imaginary
    /// [`Float`](struct.Float.html) values.
    ///
    /// This function reuses the allocated memory and does not
    /// allocate any new memory.
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (12.5, -20.75));
    /// let (real, imag) = c.into_real_imag();
    /// assert_eq!(real, 12.5);
    /// assert_eq!(imag, -20.75);
    /// ```
    #[inline]
    pub fn into_real_imag(mut self) -> (Float, Float) {
        let (mut real, mut imag) = unsafe { mem::uninitialized() };
        unsafe {
            let real_imag = self.as_mut_real_imag();
            ptr::copy_nonoverlapping(real_imag.0, &mut real, 1);
            ptr::copy_nonoverlapping(real_imag.1, &mut imag, 1);
        }
        mem::forget(self);
        (real, imag)
    }

    math_op1_no_round! {
        Complex;
        mpc::proj, rraw2;
        /// Computes a projection onto the Riemann sphere, rounding to
        /// the nearest.
        ///
        /// If no parts of the number are infinite, the number is
        /// unchanged. If any part is infinite, the real part is set
        /// to +∞ and the imaginary part is set to 0 with the same
        /// sign as the imaginary part of the original number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Complex};
        /// use std::f64;
        /// let mut c = Complex::with_val(53, (1.5, 2.5));
        /// c.proj();
        /// assert_eq!(c, (1.5, 2.5));
        /// c.assign((f64::NAN, f64::NEG_INFINITY));
        /// c.proj();
        /// assert_eq!(c, (f64::INFINITY, 0.0));
        /// // imaginary was negative, so now it is minus zero
        /// assert!(c.imag().get_sign());
        /// ```
        fn proj();
        /// Computes the projection onto the Riemann sphere.
        ///
        /// This is the reference version of the
        /// [`proj`](#method.proj) method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::f64;
        /// let c = Complex::with_val(53, (f64::INFINITY, 50));
        /// let p = Complex::with_val(53, c.proj_ref());
        /// assert_eq!(p, (f64::INFINITY, 0.0));
        /// ```
        fn proj_ref -> ProjRef;
    }
    math_op1_complex! {
        mpc::sqr;
        /// Computes the square, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, -2));
        /// // (1 - 2i) squared is (-3 - 4i)
        /// c.square();
        /// assert_eq!(c, (-3, -4));
        /// ```
        fn square();
        /// Computes the square, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut c = Complex::with_val(4, (1.25, 1.25));
        /// // (1.25 + 1.25i) squared is (0 + 3.125i).
        /// // With 4 bits of precision, 3.125 is rounded down to 3.
        /// let dir = c.square_round((Round::Down, Round::Down));
        /// assert_eq!(c, (0, 3));
        /// assert_eq!(dir, (Ordering::Equal, Ordering::Less));
        /// ```
        fn square_round;
        /// Computes the square.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let c = Complex::with_val(53, (1.25, 1.25));
        /// // (1.25 + 1.25i) squared is (0 + 3.125i).
        /// let r = c.square_ref();
        /// // With 4 bits of precision, 3.125 is rounded down to 3.
        /// let round = (Round::Down, Round::Down);
        /// let (square, dir) = Complex::with_val_round(4, r, round);
        /// assert_eq!(square, (0, 3));
        /// assert_eq!(dir, (Ordering::Equal, Ordering::Less));
        /// ```
        fn square_ref -> SquareRef;
    }
    math_op1_complex! {
        mpc::sqrt;
        /// Computes the square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (-1, 0));
        /// // square root of (-1 + 0i) is (0 + i)
        /// c.sqrt();
        /// assert_eq!(c, (0, 1));
        /// ```
        fn sqrt();
        /// Computes the square root, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::cmp::Ordering;
        /// let mut c = Complex::with_val(4, (2, 2.25));
        /// // Square root of (2 + 2.25i) is (1.5828 + 0.7108i).
        /// // Nearest with 4 bits of precision: (1.625 + 0.6875i)
        /// let dir = c.sqrt_round(Default::default());
        /// assert_eq!(c, (1.625, 0.6875));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn sqrt_round;
        /// Computes the square root.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::cmp::Ordering;
        /// let c = Complex::with_val(53, (2, 2.25));
        /// // Square root of (2 + 2.25i) is (1.5828 + 0.7108i).
        /// let r = c.sqrt_ref();
        /// // Nearest with 4 bits of precision: (1.625 + 0.6875i)
        /// let (sqrt, dir) = Complex::with_val_round(4, r, Default::default());
        /// assert_eq!(sqrt, (1.625, 0.6875));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn sqrt_ref -> SqrtRef;
    }
    math_op1_no_round! {
        Complex;
        mpc::conj, rraw2;
        /// Computes the complex conjugate.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1.5, 2.5));
        /// c.conj();
        /// assert_eq!(c, (1.5, -2.5));
        /// ```
        fn conj();
        /// Computes the complex conjugate.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, 2.5));
        /// let conj = Complex::with_val(53, c.conj_ref());
        /// assert_eq!(conj, (1.5, -2.5));
        /// ```
        fn conj_ref -> ConjugateRef;
    }

    /// Computes the absolute value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Float};
    /// use rug::float::Special;
    /// let c1 = Complex::with_val(53, (30, 40));
    /// let f1 = Float::with_val(53, c1.abs_ref());
    /// assert_eq!(f1, 50);
    /// let c2 = Complex::with_val(53, (12, Special::Infinity));
    /// let f2 = Float::with_val(53, c2.abs_ref());
    /// assert!(f2.is_infinite());
    /// ```
    #[inline]
    pub fn abs_ref(&self) -> AbsRef {
        AbsRef { ref_self: self }
    }

    /// Computes the argument.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Complex, Float};
    /// use rug::float::Special;
    /// use std::f64;
    /// // f has precision 53, just like f64, so PI constants match.
    /// let mut arg = Float::new(53);
    /// let c_pos = Complex::with_val(53, 1);
    /// arg.assign(c_pos.arg_ref());
    /// assert!(arg.is_zero());
    /// let c_neg = Complex::with_val(53, -1.3);
    /// arg.assign(c_neg.arg_ref());
    /// assert_eq!(arg, f64::consts::PI);
    /// let c_pi_4 = Complex::with_val(53, (1.333, 1.333));
    /// arg.assign(c_pi_4.arg_ref());
    /// assert_eq!(arg, f64::consts::FRAC_PI_4);
    ///
    /// // Special values are handled like atan2 in IEEE 754-2008.
    /// // Examples for real, imag set to plus, minus zero below:
    /// let mut zero = Complex::new(53);
    /// zero.assign((Special::Zero, Special::Zero));
    /// arg.assign(zero.arg_ref());
    /// assert!(arg.is_zero() && !arg.get_sign());
    /// zero.assign((Special::Zero, Special::MinusZero));
    /// arg.assign(zero.arg_ref());
    /// assert!(arg.is_zero() && arg.get_sign());
    /// zero.assign((Special::MinusZero, Special::Zero));
    /// arg.assign(zero.arg_ref());
    /// assert_eq!(arg, f64::consts::PI);
    /// zero.assign((Special::MinusZero, Special::MinusZero));
    /// arg.assign(zero.arg_ref());
    /// assert_eq!(arg, -f64::consts::PI);
    /// ```
    #[inline]
    pub fn arg_ref(&self) -> ArgRef {
        ArgRef { ref_self: self }
    }

    math_op1_complex! {
        xmpc::mul_i;
        /// Multiplies the complex number by ±<i>i</i>, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (13, 24));
        /// c.mul_i(false);
        /// assert_eq!(c, (-24, 13));
        /// c.mul_i(false);
        /// assert_eq!(c, (-13, -24));
        /// c.mul_i(true);
        /// assert_eq!(c, (-24, 13));
        /// ```
        fn mul_i(negative: bool);
        /// Multiplies the complex number by ±<i>i</i>, applying the
        /// specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // only 4 bits of precision for imaginary part
        /// let mut c = Complex::with_val((53, 4), (127, 15));
        /// assert_eq!(c, (127, 15));
        /// let dir = c.mul_i_round(false, (Round::Down, Round::Down));
        /// assert_eq!(c, (-15, 120));
        /// assert_eq!(dir, (Ordering::Equal, Ordering::Less));
        /// let dir = c.mul_i_round(true, (Round::Down, Round::Down));
        /// assert_eq!(c, (120, 15));
        /// assert_eq!(dir, (Ordering::Equal, Ordering::Equal));
        /// ```
        fn mul_i_round;
        /// Multiplies the complex number by ±<i>i</i>.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (13, 24));
        /// let rotated = Complex::with_val(53, c.mul_i_ref(false));
        /// assert_eq!(rotated, (-24, 13));
        /// ```
        fn mul_i_ref -> MulIRef;
    }
    math_op1_complex! {
        xmpc::recip;
        /// Computes the reciprocal, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// // 1/(1 + i) = (0.5 - 0.5i)
        /// c.recip();
        /// assert_eq!(c, (0.5, -0.5));
        /// ```
        fn recip();
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::cmp::Ordering;
        /// let mut c = Complex::with_val(4, (1, 2));
        /// // 1/(1 + 2i) = (0.2 - 0.4i), binary (0.00110011..., -0.01100110...)
        /// // 4 bits of precision: (0.001101, -0.01101) = (13/64, -13/32)
        /// let dir = c.recip_round(Default::default());
        /// assert_eq!(c, (13.0/64.0, -13.0/32.0));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn recip_round;
        /// Computes the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// // 1/(1 + i) = (0.5 - 0.5i)
        /// let recip = Complex::with_val(53, c.recip_ref());
        /// assert_eq!(recip, (0.5, -0.5));
        /// ```
        fn recip_ref -> RecipRef;
    }

    /// Computes the norm, that is the square of the absolute value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Float};
    /// let c = Complex::with_val(53, (3, 4));
    /// let f = Float::with_val(53, c.norm_ref());
    /// assert_eq!(f, 25);
    /// ```
    #[inline]
    pub fn norm_ref(&self) -> NormRef {
        NormRef { ref_self: self }
    }

    math_op1_complex! {
        mpc::log;
        /// Computes the natural logarithm, rounding to the nearest.
        fn ln();
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        fn ln_round;
        /// Computes the natural logarithm;
        fn ln_ref -> LnRef;
    }
    math_op1_complex! {
        mpc::log10;
        /// Computes the logarithm to base 10, rounding to the nearest.
        fn log10();
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        fn log10_round;
        /// Computes the logarithm to base 10.
        fn log10_ref -> Log10Ref;
    }
    math_op1_complex! {
        mpc::exp;
        /// Computes the exponential, rounding to the nearest.
        fn exp();
        /// Computes the exponential, applying the specified rounding
        /// method.
        fn exp_round;
        /// Computes the exponential.
        fn exp_ref -> ExpRef;
    }
    math_op1_complex! {
        mpc::sin;
        /// Computes the sine, rounding to the nearest.
        fn sin();
        /// Computes the sine, applying the specified rounding method.
        fn sin_round;
        /// Computes the sine.
        fn sin_ref -> SinRef;
    }
    math_op1_complex! {
        mpc::cos;
        /// Computes the cosine, rounding to the nearest.
        fn cos();
        /// Computes the cosine, applying the specified rounding method.
        fn cos_round;
        /// Computes the cosine.
        fn cos_ref -> CosRef;
    }
    math_op1_2_complex! {
        mpc::sin_cos;
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos(cos);
        /// Computes the sine and cosine of `self`, applying the
        /// specified rounding methods.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos_round;
        /// Computes the sine and cosine.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Complex};
        /// // sin(0.5 + 0.2i) = 0.48905 + 0.17669i
        /// // cos(0.5 + 0.2i) = 0.89519 - 0.096526i
        /// let angle = Complex::with_val(53, (0.5, 0.2));
        /// let r = angle.sin_cos_ref();
        /// // use only 10 bits of precision here to
        /// // make comparison easier
        /// let (mut sin, mut cos) = (Complex::new(10), Complex::new(10));
        /// (&mut sin, &mut cos).assign(r);
        /// assert_eq!(sin, Complex::with_val(10, (0.48905, 0.17669)));
        /// assert_eq!(cos, Complex::with_val(10, (0.89519, -0.096526)));
        fn sin_cos_ref -> SinCosRef;
    }
    math_op1_complex! {
        mpc::tan;
        /// Computes the tangent, rounding to the nearest.
        fn tan();
        /// Computes the tangent, applying the specified rounding method.
        fn tan_round;
        /// Computes the tangent.
        fn tan_ref -> TanRef;
    }
    math_op1_complex! {
        mpc::sinh;
        /// Computes the hyperbolic sine, rounding to the nearest.
        fn sinh();
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        fn sinh_round;
        /// Computes the hyperbolic sine.
        fn sinh_ref -> SinhRef;
    }
    math_op1_complex! {
        mpc::cosh;
        /// Computes the hyperbolic cosine, rounding to the nearest.
        fn cosh();
        /// Computes the hyperbolic cosine, applying the specified rounding
        /// method.
        fn cosh_round;
        /// Computes the hyperbolic cosine.
        fn cosh_ref -> CoshRef;
    }
    math_op1_complex! {
        mpc::tanh;
        /// Computes the hyperbolic tangent, rounding to the nearest.
        fn tanh();
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        fn tanh_round;
        /// Computes the hyperbolic tangent.
        fn tanh_ref -> TanhRef;
    }
    math_op1_complex! {
        mpc::asin;
        /// Computes the inverse sine, rounding to the nearest.
        fn asin();
        /// Computes the inverse sine, applying the specified rounding
        /// method.
        fn asin_round;
        /// Computes the inverse sine.
        fn asin_ref -> AsinRef;
    }
    math_op1_complex! {
        mpc::acos;
        /// Computes the inverse cosine, rounding to the nearest.
        fn acos();
        /// Computes the inverse cosine, applying the specified rounding
        /// method.
        fn acos_round;
        /// Computes the inverse cosine.
        fn acos_ref -> AcosRef;
    }
    math_op1_complex! {
        mpc::atan;
        /// Computes the inverse tangent, rounding to the nearest.
        fn atan();
        /// Computes the inverse tangent, applying the specified rounding
        /// method.
        fn atan_round;
        /// Computes the inverse tangent.
        fn atan_ref -> AtanRef;
    }
    math_op1_complex! {
        mpc::asinh;
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        fn asinh();
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        fn asinh_round;
        /// Computes the inverse hyperboic sine.
        fn asinh_ref -> AsinhRef;
    }
    math_op1_complex! {
        mpc::acosh;
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        fn acosh();
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        fn acosh_round;
        /// Computes the inverse hyperbolic cosine.
        fn acosh_ref -> AcoshRef;
    }
    math_op1_complex! {
        mpc::atanh;
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        fn atanh();
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        fn atanh_round;
        /// Computes the inverse hyperbolic tangent.
        fn atanh_ref -> AtanhRef;
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits(rng)`][equiv] on the real part, and then
    /// calling the same method on the imaginary part.
    ///
    /// [equiv]: struct.Float.html#method.assign_random_bits
    #[inline]
    pub fn assign_random_bits(
        &mut self,
        rng: &mut RandState,
    ) -> Result<(), ()> {
        let (real, imag) = self.as_mut_real_imag();
        real.assign_random_bits(rng)?;
        imag.assign_random_bits(rng)
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number, rounding to the nearest.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_cont_round).
    #[inline]
    pub fn assign_random_cont(&mut self, rng: &mut RandState) {
        self.assign_random_cont_round(rng, Default::default());
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number, applying the specified
    /// rounding method.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, round.0)`]
    /// (struct.Float.html#method.assign_random_bits_round) on the
    /// real part, and then calling the same method with `round.1` on
    /// the imaginary part.
    #[inline]
    pub fn assign_random_cont_round(
        &mut self,
        rng: &mut RandState,
        round: Round2,
    ) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (
            real.assign_random_cont_round(rng, round.0),
            imag.assign_random_cont_round(rng, round.1),
        )
    }
}

impl From<(Float, Float)> for Complex {
    /// Constructs a `Complex` number from a real
    /// [`Float`](struct.Float.html) and imaginary
    /// [`Float`](struct.Float.html).
    ///
    /// This constructor does not allocate, as it reuses the
    /// [`Float`](struct.Float.html) components.
    #[inline]
    fn from((real, imag): (Float, Float)) -> Complex {
        let mut dst: Complex = unsafe { mem::uninitialized() };
        unsafe {
            let mut real_imag = dst.as_mut_real_imag();
            ptr::copy_nonoverlapping(&real, real_imag.0, 1);
            ptr::copy_nonoverlapping(&imag, real_imag.1, 1);
        }
        mem::forget(real);
        mem::forget(imag);
        dst
    }
}

impl Display for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

impl<T> Assign<T> for Complex
where
    Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>,
{
    #[inline]
    fn assign(&mut self, other: T) {
        self.assign_round(other, Default::default());
    }
}

impl AssignRound<Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, other: Complex, round: Round2) -> Ordering2 {
        self.assign_round(&other, round)
    }
}

impl<'a> AssignRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, other: &Complex, round: Round2) -> Ordering2 {
        let ret =
            unsafe { mpc::set(self.inner_mut(), other.inner(), rraw2(round)) };
        ordering2(ret)
    }
}

macro_rules! assign_ref {
    { $T:ty } => {
        impl<'a> AssignRound<&'a $T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            #[inline]
            fn assign_round(
                &mut self,
                other: &'a $T,
                round: Round2,
            ) -> Ordering2 {
                let (real, imag) = self.as_mut_real_imag();
                let ord1 = real.assign_round(other, round.0);
                let ord2 = imag.assign_round(0, round.1);
                (ord1, ord2)
            }
        }
    };
}

macro_rules! assign {
    { $T:ty } => {
        impl AssignRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            #[inline]
            fn assign_round(&mut self, other: $T, round: Round2) -> Ordering2 {
                let (real, imag) = self.as_mut_real_imag();
                let ord1 = real.assign_round(other, round.0);
                let ord2 = imag.assign_round(0, round.1);
                (ord1, ord2)
            }
        }
    };
}

#[cfg(feature = "integer")]
assign_ref! { Integer }
#[cfg(feature = "rational")]
assign_ref! { Rational }
assign_ref! { Float }
#[cfg(feature = "integer")]
assign! { Integer }
#[cfg(feature = "rational")]
assign! { Rational }
assign! { Float }
assign! { Special }
assign! { Constant }
assign! { i32 }
assign! { i64 }
assign! { u32 }
assign! { u64 }
assign! { f32 }
assign! { f64 }

impl<T, U> AssignRound<(T, U)> for Complex
where
    Float: AssignRound<T, Round = Round, Ordering = Ordering>,
    Float: AssignRound<U, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, other: (T, U), round: Round2) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        let ord1 = real.assign_round(other.0, round.0);
        let ord2 = imag.assign_round(other.1, round.1);
        (ord1, ord2)
    }
}

ref_math_op1_complex! { mpc::proj; struct ProjRef {} }
ref_math_op1_complex! { mpc::sqr; struct SquareRef {} }
ref_math_op1_complex! { mpc::sqrt; struct SqrtRef {} }
ref_math_op1_complex! { mpc::conj; struct ConjugateRef {} }

pub struct AbsRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<AbsRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: AbsRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::abs(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

pub struct ArgRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<ArgRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: ArgRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::arg(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

ref_math_op1_complex! { xmpc::mul_i; struct MulIRef { negative: bool } }
ref_math_op1_complex! { xmpc::recip; struct RecipRef {} }

pub struct NormRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<NormRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NormRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::norm(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

ref_math_op1_complex! { mpc::log; struct LnRef {} }
ref_math_op1_complex! { mpc::log10; struct Log10Ref {} }
ref_math_op1_complex! { mpc::exp; struct ExpRef {} }
ref_math_op1_complex! { mpc::sin; struct SinRef {} }
ref_math_op1_complex! { mpc::cos; struct CosRef {} }
ref_math_op1_2_complex! { mpc::sin_cos; struct SinCosRef {} }
ref_math_op1_complex! { mpc::tan; struct TanRef {} }
ref_math_op1_complex! { mpc::sinh; struct SinhRef {} }
ref_math_op1_complex! { mpc::cosh; struct CoshRef {} }
ref_math_op1_complex! { mpc::tanh; struct TanhRef {} }
ref_math_op1_complex! { mpc::asin; struct AsinRef {} }
ref_math_op1_complex! { mpc::acos; struct AcosRef {} }
ref_math_op1_complex! { mpc::atan; struct AtanRef {} }
ref_math_op1_complex! { mpc::asinh; struct AsinhRef {} }
ref_math_op1_complex! { mpc::acosh; struct AcoshRef {} }
ref_math_op1_complex! { mpc::atanh; struct AtanhRef {} }

impl Neg for Complex {
    type Output = Complex;
    #[inline]
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    #[inline]
    fn neg_assign(&mut self) {
        unsafe {
            mpc::neg(self.inner_mut(), self.inner(), rraw2(Default::default()));
        }
    }
}

impl<'a> Neg for &'a Complex {
    type Output = NegRef<'a>;
    #[inline]
    fn neg(self) -> NegRef<'a> {
        NegRef { val: self }
    }
}

pub struct NegRef<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<NegRef<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: NegRef<'a>, round: Round2) -> Ordering2 {
        let ret = unsafe {
            mpc::neg(self.inner_mut(), src.val.inner(), rraw2(round))
        };
        ordering2(ret)
    }
}

macro_rules! arith_binary_self_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Ref:ident
    } => {
        arith_binary_self_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Ref
        }
    }
}

macro_rules! arith_forward_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident
    } => {
        arith_forward_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $RefOwn
        }
    }
}

macro_rules! arith_commut_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident
    } => {
        arith_commut_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefOwn
        }
    }
}

macro_rules! arith_noncommut_complex {
    {
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefFrom:ident $RefOwn:ident $RefFromOwn:ident
    } => {
        arith_noncommut_round! {
            Complex, Round2 => Ordering2;
            $func, $func_from, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefFrom $RefOwn $RefFromOwn
        }
    }
}

arith_binary_self_complex! {
    mpc::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddRef
}
arith_binary_self_complex! {
    mpc::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubRef
}
arith_binary_self_complex! {
    mpc::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulRef
}
arith_binary_self_complex! {
    mpc::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivRef
}
arith_binary_self_complex! {
    mpc::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowRef
}

arith_commut_complex! {
    mpc::add_fr;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Float;
    AddRefFloat AddRefFloatOwn
}
arith_noncommut_complex! {
    mpc::sub_fr, mpc::fr_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Float;
    SubRefFloat SubFromRefFloat SubRefFloatOwn SubFromRefFloatOwn
}
arith_commut_complex! {
    mpc::mul_fr;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Float;
    MulRefFloat MulRefFloatOwn
}
arith_noncommut_complex! {
    mpc::div_fr, mpc::fr_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Float;
    DivRefFloat DivFromRefFloat DivRefFloatOwn DivFromRefFloatOwn
}
arith_forward_complex! {
    mpc::pow_fr;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Float;
    PowRefFloat PowRefFloatOwn
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    mpc::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowRefInteger PowRefIntegerOwn
}

macro_rules! arith_prim_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_exact_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_exact_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_commut_complex {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_commut_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_noncommut_complex {
    {
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $RefFrom:ident
    } => {
        arith_prim_noncommut_round! {
            Complex, Round2 => Ordering2;
            $func, $func_from, rraw2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefFrom
        }
    }
}

arith_prim_commut_complex! {
    mpc::add_ui;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    u32;
    AddRefU32
}
arith_prim_noncommut_complex! {
    mpc::sub_ui, xmpc::ui_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    u32;
    SubRefU32 SubFromRefU32
}
arith_prim_commut_complex! {
    mpc::mul_ui;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    u32;
    MulRefU32
}
arith_prim_noncommut_complex! {
    mpc::div_ui, xmpc::ui_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    u32;
    DivRefU32 DivFromRefU32
}
arith_prim_commut_complex! {
    xmpc::add_si;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    i32;
    AddRefI32
}
arith_prim_noncommut_complex! {
    xmpc::sub_si, xmpc::si_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    i32;
    SubRefI32 SubFromRefI32
}
arith_prim_commut_complex! {
    mpc::mul_si;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    i32;
    MulRefI32
}
arith_prim_noncommut_complex! {
    xmpc::div_si, xmpc::si_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    i32;
    DivRefI32 DivFromRefI32
}

arith_prim_exact_complex! {
    mpc::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlRefU32
}
arith_prim_exact_complex! {
    mpc::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrRefU32
}
arith_prim_complex! {
    mpc::pow_ui;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    u32;
    PowRefU32
}
arith_prim_exact_complex! {
    mpc::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlRefI32
}
arith_prim_exact_complex! {
    mpc::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrRefI32
}
arith_prim_complex! {
    mpc::pow_si;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    i32;
    PowRefI32
}
arith_prim_complex! {
    mpc::pow_d;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f64;
    PowRefF64
}
arith_prim_complex! {
    xmpc::pow_f32;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f32;
    PowRefF32
}

impl<'a> Add<MulRef<'a>> for Complex {
    type Output = Complex;
    /// Peforms multiplication and addition together, with only one
    /// rounding operation to the nearest.
    #[inline]
    fn add(mut self, rhs: MulRef) -> Complex {
        self.add_assign(rhs);
        self
    }
}

impl<'a> AddAssign<MulRef<'a>> for Complex {
    /// Peforms multiplication and addition together, with only one
    /// rounding operation to the nearest.
    #[inline]
    fn add_assign(&mut self, rhs: MulRef) {
        self.add_assign_round(rhs, Default::default());
    }
}

impl<'a> AddAssignRound<MulRef<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    /// Peforms multiplication and addition together with only one
    /// rounding operation as specified.
    #[inline]
    fn add_assign_round(&mut self, rhs: MulRef, round: Round2) -> Ordering2 {
        let ret = unsafe {
            mpc::fma(
                self.inner_mut(),
                rhs.lhs.inner(),
                rhs.rhs.inner(),
                self.inner(),
                rraw2(round),
            )
        };
        ordering2(ret)
    }
}

impl PartialEq for Complex {
    #[inline]
    fn eq(&self, other: &Complex) -> bool {
        self.real().eq(other.real()) && self.imag().eq(other.imag())
    }
}

impl<T, U> PartialEq<(T, U)> for Complex
where
    Float: PartialEq<T>,
    Float: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &(T, U)) -> bool {
        self.real().eq(&other.0) && self.imag().eq(&other.1)
    }
}

macro_rules! partial_eq {
    { $T:ty } => {
        impl PartialEq<$T> for Complex {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.real().eq(other) && self.imag().is_zero()
            }
        }
    }
}

#[cfg(feature = "integer")]
partial_eq! { Integer }
#[cfg(feature = "rational")]
partial_eq! { Rational }
partial_eq! { Float }
partial_eq! { u32 }
partial_eq! { i32 }
partial_eq! { f64 }
partial_eq! { f32 }

fn fmt_radix(
    c: &Complex,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) -> fmt::Result {
    let (real, imag) = c.as_real_imag();
    let mut buf = String::from("(");
    fmt_float(&mut buf, real, fmt, radix, to_upper, prefix, show_neg_zero);
    buf.push(' ');
    fmt_float(&mut buf, imag, fmt, radix, to_upper, prefix, show_neg_zero);
    buf.push(')');
    let count = buf.chars().count();
    let padding = match fmt.width() {
        Some(width) if width > count => width - count,
        _ => return fmt.write_str(&buf),
    };
    let mut fill_buf = String::with_capacity(4);
    fill_buf.push(fmt.fill());
    for _ in 0..padding {
        fmt.write_str(&fill_buf)?;
    }
    fmt.write_str(&buf)
}

fn fmt_float(
    buf: &mut String,
    flt: &Float,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) {
    let show_neg_zero = show_neg_zero || fmt.sign_plus();
    let mut s = flt.to_string_radix(radix, fmt.precision());
    let minus = s.starts_with('-') ||
        (show_neg_zero && flt.is_zero() && flt.get_sign());
    if minus {
        buf.push('-');
    } else if fmt.sign_plus() {
        buf.push('+');
    }
    if fmt.alternate() {
        buf.push_str(prefix);
    }
    if to_upper && flt.is_finite() {
        s.make_ascii_uppercase();
    }
    buf.push_str(if s.starts_with('-') { &s[1..] } else { &s });
}

/// A validated string that can always be converted to a `Complex`.
///
/// See the [`Complex::valid_str_radix`]
/// (../struct.Complex.html#method.valid_str_radix) method.
#[derive(Clone, Debug)]
pub struct ValidComplex<'a> {
    poss: ValidPoss<'a>,
}

#[derive(Clone, Debug)]
enum ValidPoss<'a> {
    Real(ValidFloat<'a>),
    Complex(ValidFloat<'a>, ValidFloat<'a>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// An error which can be returned when parsing a `Complex` number.
pub struct ParseComplexError {
    kind: ParseErrorKind,
}

impl<'a> AssignRound<ValidComplex<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, rhs: ValidComplex, round: Round2) -> Ordering2 {
        match rhs.poss {
            ValidPoss::Real(re) => {
                let real_ord = self.mut_real().assign_round(re, round.0);
                self.mut_imag().assign(Special::Zero);
                (real_ord, Ordering::Equal)
            }
            ValidPoss::Complex(re, im) => {
                let real_ord = self.mut_real().assign_round(re, round.0);
                let imag_ord = self.mut_imag().assign_round(im, round.1);
                (real_ord, imag_ord)
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    InvalidFloat(ParseFloatError),
    InvalidRealFloat(ParseFloatError),
    InvalidImagFloat(ParseFloatError),
    MissingSpace,
    MissingClose,
    CloseNotLast,
}

impl Error for ParseComplexError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidFloat(_) => "string is not a valid float",
            InvalidRealFloat(_) => "real part of string is not a valid float",
            InvalidImagFloat(_) => {
                "imaginary part of string is not a valid float"
            }
            MissingSpace => "string has no space after opening bracket",
            MissingClose => "string has no closing bracket",
            CloseNotLast => "string has more characters after closing bracket",
        }
    }
}

impl Display for ParseComplexError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}

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

#[inline]
fn rraw2(round: Round2) -> mpc::rnd_t {
    match (round.0, round.1) {
        (Round::Nearest, Round::Nearest) => mpc::RNDNN,
        (Round::Nearest, Round::Zero) => mpc::RNDNZ,
        (Round::Nearest, Round::Up) => mpc::RNDNU,
        (Round::Nearest, Round::Down) => mpc::RNDND,
        (Round::Zero, Round::Nearest) => mpc::RNDZN,
        (Round::Zero, Round::Zero) => mpc::RNDZZ,
        (Round::Zero, Round::Up) => mpc::RNDZU,
        (Round::Zero, Round::Down) => mpc::RNDZD,
        (Round::Up, Round::Nearest) => mpc::RNDUN,
        (Round::Up, Round::Zero) => mpc::RNDUZ,
        (Round::Up, Round::Up) => mpc::RNDUU,
        (Round::Up, Round::Down) => mpc::RNDUD,
        (Round::Down, Round::Nearest) => mpc::RNDDN,
        (Round::Down, Round::Zero) => mpc::RNDDZ,
        (Round::Down, Round::Up) => mpc::RNDDU,
        (Round::Down, Round::Down) => mpc::RNDDD,
        (Round::AwayFromZero, _) |
        (_, Round::AwayFromZero) => unimplemented!(),
    }
}

#[inline]
fn ordering2(ord: c_int) -> Ordering2 {
    // ord == first + 4 * second
    let first = mpc::INEX_RE(ord).cmp(&0);
    let second = mpc::INEX_IM(ord).cmp(&0);
    (first, second)
}

#[inline]
fn ordering4(ord: c_int) -> (Ordering2, Ordering2) {
    (ordering2(mpc::INEX1(ord)), ordering2(mpc::INEX2(ord)))
}

impl Inner for Complex {
    type Output = mpc_t;
    #[inline]
    fn inner(&self) -> &mpc_t {
        &self.inner
    }
}

impl InnerMut for Complex {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut mpc_t {
        &mut self.inner
    }
}
