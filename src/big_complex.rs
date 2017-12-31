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

use {Assign, Float};
use big_float;
use complex::{OrdComplex, Prec};
use ext::mpc as xmpc;
use float::{self, ParseFloatError, Round, Special, ValidFloat};
use gmp_mpfr_sys::mpc::{self, mpc_t};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
#[cfg(feature = "rand")]
use misc;
use ops::{AssignRound, AssignRoundInto, NegAssign};
#[cfg(feature = "rand")]
use ops::AssignInto;
#[cfg(feature = "rand")]
use rand::RandState;
use std::cmp::Ordering;
use std::error::Error;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::ptr;
use std::slice;

pub type Round2 = (Round, Round);

pub type Ordering2 = (Ordering, Ordering);

/// A multi-precision complex number with arbitrarily large precision
/// and correct rounding.
///
/// The precision has to be set during construction. The rounding
/// method of the required operations can be specified, and the
/// direction of the rounding is returned.
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
/// Operations on two borrowed `Complex` numbers result in an
/// intermediate value that has to be assigned to a new `Complex`
/// value.
///
/// ```rust
/// use rug::Complex;
/// let a = Complex::with_val(53, (10.5, -11));
/// let b = Complex::with_val(53, (-1.25, -1.5));
/// let a_b_ref = &a + &b;
/// let a_b = Complex::with_val(53, a_b_ref);
/// assert_eq!(a_b, (9.25, -12.5));
/// ```
///
/// As a special case, when an intermediate value is obtained from
/// multiplying two `Complex` references, it can be added to or
/// subtracted from another `Complex` (or reference). This will result
/// in a fused multiply-accumulate operation, with only one rounding
/// operation taking place.
///
/// ```rust
/// use rug::Complex;
/// let mut acc = Complex::with_val(53, (1000, 1000));
/// let m1 = Complex::with_val(53, (10, 0));
/// let m2 = Complex::with_val(53, (1, -1));
/// // (1000 + 1000i) - (10 + 0i) * (1 - i) = (990 + 1010i)
/// acc -= &m1 * &m2;
/// assert_eq!(acc, (990, 1010));
/// ```
///
/// The `Complex` type supports various functions. Most methods have
/// four versions:
///
/// 1. The first method consumes the operand and rounds the returned
///    `Complex` to the [nearest](float/enum.Round.html#variant.Nearest)
///    representable value.
/// 2. The second method has a `_mut` suffix, mutates the operand and
///    rounds it the nearest representable value.

/// 3. The third method has a `_round` suffix, mutates the operand,
///    applies the specified [rounding method](float/enum.Round.html)
///    to the real and imaginary parts, and returns the rounding
///    direction for both:
///    * `Ordering::Less` if the stored part is less than the exact
///      result,
///    * `Ordering::Equal` if the stored part is equal to the exact
///      result,
///    * `Ordering::Greater` if the stored part is greater than the
///      exact result.
/// 4. The fourth method has a `_ref` suffix and borrows the operand.
///    The returned item can be assigned to a `Complex`, and the
///    rounding method is selected during the assignment.
///
/// ```rust
/// use rug::Complex;
/// use rug::float::Round;
/// use std::cmp::Ordering;
/// let expected = Complex::with_val(53, (1.2985, 0.6350));
///
/// // 1. consume the operand, round to nearest
/// let a = Complex::with_val(53, (1, 1));
/// let sin_a = a.sin();
/// assert!((sin_a - &expected).abs() < 0.0001);
///
/// // 2. mutate the operand, round to nearest
/// let mut b = Complex::with_val(53, (1, 1));
/// b.sin_mut();
/// assert!((b - &expected).abs() < 0.0001);
///
/// // 3. mutate the operand, apply specified rounding
/// let mut c = Complex::with_val(4, (1, 1));
/// // using 4 significant bits, 1.2985 is rounded down to 1.25
/// // and 0.6350 is rounded down to 0.625.
/// let dir = c.sin_round((Round::Nearest, Round::Nearest));
/// assert_eq!(c, (1.25, 0.625));
/// assert_eq!(dir, (Ordering::Less, Ordering::Less));
///
/// // 4. borrow the operand
/// let d = Complex::with_val(53, (1, 1));
/// let r = d.sin_ref();
/// let sin_d = Complex::with_val(53, r);
/// assert!((sin_d - &expected).abs() < 0.0001);
/// // d was not consumed
/// assert_eq!(d, (1, 1));
/// ```
pub struct Complex {
    inner: mpc_t,
}

macro_rules! ref_math_op0_complex {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        ref_math_op0_round! {
            Complex, Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $(#[$attr_ref])*
            struct $Ref { $($param: $T),* }
        }
    }
}

macro_rules! math_op1_complex {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        math_op1_round! {
            Round2 => Ordering2;
            $func, rraw2 => ordering2;
            $(#[$attr])*
            fn $method($($param: $T),*);
            $(#[$attr_mut])*
            fn $method_mut;
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
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        math_op1_2_round! {
            Round2 => (Ordering2, Ordering2);
            $func, rraw2, rraw2 => ordering4;
            $(#[$attr])*
            fn $method($rop $(, $param: $T)*);
            $(#[$attr_mut])*
            fn $method_mut;
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
            p.0 >= float::prec_min() && p.0 <= float::prec_max()
                && p.1 >= float::prec_min()
                && p.1 <= float::prec_max(),
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
            let space = src.find(' ').ok_or(Error {
                kind: Kind::MissingSpace,
            })?;
            let real_str = &src[1..space];
            let re =
                Float::valid_str_radix(real_str, radix).map_err(|e| Error {
                    kind: Kind::InvalidRealFloat(e),
                })?;
            let rest = &src[space + 1..];
            let close = rest.find(')').ok_or(Error {
                kind: Kind::MissingClose,
            })?;
            let imag_str = &rest[0..close];
            let im =
                Float::valid_str_radix(imag_str, radix).map_err(|e| Error {
                    kind: Kind::InvalidImagFloat(e),
                })?;
            if close != rest.len() - 1 {
                return Err(Error {
                    kind: Kind::CloseNotLast,
                });
            }
            ValidPoss::Complex(re, im)
        } else {
            let re = Float::valid_str_radix(src, radix).map_err(|e| Error {
                kind: Kind::InvalidFloat(e),
            })?;
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
        let mut s = String::new();
        append_to_string(
            &mut s,
            self,
            radix,
            num_digits,
            round,
            false,
            false,
            "",
        );
        s
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
        Ok(self.assign_round(Complex::valid_str_radix(src, radix)?, round))
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
        unsafe { &*(mpc::realref_const(self.inner()) as *const _) }
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
        unsafe { &*(mpc::imagref_const(self.inner()) as *const _) }
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
        unsafe { &mut *(mpc::realref(self.inner_mut()) as *mut _) }
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
        unsafe { &mut *(mpc::imagref(self.inner_mut()) as *mut _) }
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
            (
                &mut *(mpc::realref(self.inner_mut()) as *mut _),
                &mut *(mpc::imagref(self.inner_mut()) as *mut _),
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
    pub fn into_real_imag(self) -> (Float, Float) {
        let (mut real, mut imag) = unsafe { mem::uninitialized() };
        unsafe {
            let real_imag = self.as_real_imag();
            ptr::copy_nonoverlapping(real_imag.0, &mut real, 1);
            ptr::copy_nonoverlapping(real_imag.1, &mut imag, 1);
        }
        mem::forget(self);
        (real, imag)
    }

    /// Borrows a negated copy of the `Complex` number.
    ///
    /// The returned object implements `Deref<Complex>`.
    ///
    /// This method performs a shallow copy and negates it, and
    /// negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (4.2, -2.3));
    /// let neg_c = c.as_neg();
    /// assert_eq!(*neg_c, (-4.2, 2.3));
    /// // methods taking &self can be used on the returned object
    /// let reneg_c = neg_c.as_neg();
    /// assert_eq!(*reneg_c, (4.2, -2.3));
    /// assert_eq!(*reneg_c, c);
    /// ```
    pub fn as_neg(&self) -> BorrowComplex {
        // shallow copy
        let mut ret = BorrowComplex {
            inner: self.inner,
            phantom: PhantomData,
        };
        unsafe {
            (*mpc::realref(&mut ret.inner)).sign.neg_assign();
            (*mpc::imagref(&mut ret.inner)).sign.neg_assign();
            if self.real().is_nan() || self.imag().is_nan() {
                mpfr::set_nanflag();
            }
        }
        ret
    }

    /// Borrows a conjugate copy of the `Complex` number.
    ///
    /// The returned object implements `Deref<Complex>`.
    ///
    /// This method performs a shallow copy and negates its imaginary
    /// part, and negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (4.2, -2.3));
    /// let conj_c = c.as_conj();
    /// assert_eq!(*conj_c, (4.2, 2.3));
    /// // methods taking &self can be used on the returned object
    /// let reconj_c = conj_c.as_conj();
    /// assert_eq!(*reconj_c, (4.2, -2.3));
    /// assert_eq!(*reconj_c, c);
    /// ```
    pub fn as_conj(&self) -> BorrowComplex {
        let mut ret = BorrowComplex {
            inner: self.inner,
            phantom: PhantomData,
        };
        unsafe {
            (*mpc::imagref(&mut ret.inner)).sign.neg_assign();
            if self.imag().is_nan() {
                mpfr::set_nanflag();
            }
        }
        ret
    }

    /// Borrows a rotated copy of the `Complex` number.
    ///
    /// The returned object implements `Deref<Complex>`.
    ///
    /// This method operates by performing some shallow copying;
    /// unlike the [`mul_i`](#method.mul_i) method and friends, this
    /// method swaps the precision of the real and imaginary parts if
    /// they have unequal precisions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (4.2, -2.3));
    /// let mul_i_c = c.as_mul_i(false);
    /// assert_eq!(*mul_i_c, (2.3, 4.2));
    /// // methods taking &self can be used on the returned object
    /// let mul_ii_c = mul_i_c.as_mul_i(false);
    /// assert_eq!(*mul_ii_c, (-4.2, 2.3));
    /// let mul_1_c = mul_i_c.as_mul_i(true);
    /// assert_eq!(*mul_1_c, (4.2, -2.3));
    /// assert_eq!(*mul_1_c, c);
    /// ```
    pub fn as_mul_i(&self, negative: bool) -> BorrowComplex {
        let mut ret = BorrowComplex {
            inner: unsafe { mem::uninitialized() },
            phantom: PhantomData,
        };
        let (ret_re, ret_im) = unsafe {
            let re = &mut *mpc::realref(&mut ret.inner);
            let im = &mut *mpc::imagref(&mut ret.inner);
            ptr::copy_nonoverlapping(self.real().inner(), im, 1);
            ptr::copy_nonoverlapping(self.imag().inner(), re, 1);
            (re, im)
        };
        if negative {
            ret_im.sign.neg_assign();
        } else {
            ret_re.sign.neg_assign();
        }
        if self.real().is_nan() || self.imag().is_nan() {
            unsafe {
                mpfr::set_nanflag();
            }
        }
        ret
    }

    /// Borrows the `Complex` as an ordered complex number of type
    /// [`OrdComplex`](complex/struct.OrdComplex.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Special;
    /// use std::cmp::Ordering;
    ///
    /// let nan_c = Complex::with_val(53, (Special::Nan, Special::Nan));
    /// let nan = nan_c.as_ord();
    /// assert_eq!(nan.cmp(nan), Ordering::Equal);
    ///
    /// let one_neg0_c = Complex::with_val(53, (1, Special::NegZero));
    /// let one_neg0 = one_neg0_c.as_ord();
    /// let one_pos0_c = Complex::with_val(53, (1, Special::Zero));
    /// let one_pos0 = one_pos0_c.as_ord();
    /// assert_eq!(one_neg0.cmp(one_pos0), Ordering::Less);
    ///
    /// let zero_inf_s = (Special::Zero, Special::Infinity);
    /// let zero_inf_c = Complex::with_val(53, zero_inf_s);
    /// let zero_inf = zero_inf_c.as_ord();
    /// assert_eq!(one_pos0.cmp(zero_inf), Ordering::Greater);
    /// ```
    pub fn as_ord(&self) -> &OrdComplex {
        unsafe { &*(self as *const _ as *const _) }
    }

    /// Compares the absolute values of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use std::cmp::Ordering;
    /// let a = Complex::with_val(53, (5, 0));
    /// let b = Complex::with_val(53, (3, -4));
    /// let c = Complex::with_val(53, (-4, -4));
    /// assert_eq!(a.cmp_abs(&b), Some(Ordering::Equal));
    /// assert_eq!(a.cmp_abs(&c), Some(Ordering::Less));
    /// ```
    #[inline]
    pub fn cmp_abs(&self, other: &Complex) -> Option<Ordering> {
        unsafe {
            if self.real().is_nan() || self.imag().is_nan()
                || other.real().is_nan() || other.imag().is_nan()
            {
                None
            } else {
                Some(ordering1(mpc::cmp_abs(self.inner(), other.inner())))
            }
        }
    }

    math_op1_no_round! {
        mpc::proj, rraw2;
        /// Computes a projection onto the Riemann sphere, rounding to
        /// the nearest.
        ///
        /// If no parts of the number are infinite, the result is
        /// unchanged. If any part is infinite, the real part of the
        /// result is set to +∞ and the imaginary part of the result
        /// is set to 0 with the same sign as the imaginary part of
        /// the input.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::f64;
        /// let c1 = Complex::with_val(53, (1.5, 2.5));
        /// let proj1 = c1.proj();
        /// assert_eq!(proj1, (1.5, 2.5));
        /// let c2 = Complex::with_val(53, (f64::NAN, f64::NEG_INFINITY));
        /// let proj2 = c2.proj();
        /// assert_eq!(proj2, (f64::INFINITY, 0.0));
        /// // imaginary was negative, so now it is minus zero
        /// assert!(proj2.imag().is_sign_negative());
        /// ```
        fn proj();
        /// Computes a projection onto the Riemann sphere, rounding to
        /// the nearest.
        ///
        /// If no parts of the number are infinite, the result is
        /// unchanged. If any part is infinite, the real part of the
        /// result is set to +∞ and the imaginary part of the result
        /// is set to 0 with the same sign as the imaginary part of
        /// the input.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::f64;
        /// let mut c1 = Complex::with_val(53, (1.5, 2.5));
        /// c1.proj_mut();
        /// assert_eq!(c1, (1.5, 2.5));
        /// let mut c2 = Complex::with_val(53, (f64::NAN, f64::NEG_INFINITY));
        /// c2.proj_mut();
        /// assert_eq!(c2, (f64::INFINITY, 0.0));
        /// // imaginary was negative, so now it is minus zero
        /// assert!(c2.imag().is_sign_negative());
        /// ```
        fn proj_mut;
        /// Computes the projection onto the Riemann sphere.
        ///
        /// If no parts of the number are infinite, the result is
        /// unchanged. If any part is infinite, the real part of the
        /// result is set to +∞ and the imaginary part of the result
        /// is set to 0 with the same sign as the imaginary part of
        /// the input.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use std::f64;
        /// let c1 = Complex::with_val(53, (f64::INFINITY, 50));
        /// let proj1 = Complex::with_val(53, c1.proj_ref());
        /// assert_eq!(proj1, (f64::INFINITY, 0.0));
        /// let c2 = Complex::with_val(53, (f64::NAN, f64::NEG_INFINITY));
        /// let proj2 = Complex::with_val(53, c2.proj_ref());
        /// assert_eq!(proj2, (f64::INFINITY, 0.0));
        /// // imaginary was negative, so now it is minus zero
        /// assert!(proj2.imag().is_sign_negative());
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
        /// let c = Complex::with_val(53, (1, -2));
        /// // (1 - 2i) squared is (-3 - 4i)
        /// let square = c.square();
        /// assert_eq!(square, (-3, -4));
        /// ```
        fn square();
        /// Computes the square, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, -2));
        /// // (1 - 2i) squared is (-3 - 4i)
        /// c.square_mut();
        /// assert_eq!(c, (-3, -4));
        /// ```
        fn square_mut;
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
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
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
        /// let c = Complex::with_val(53, (-1, 0));
        /// // square root of (-1 + 0i) is (0 + i)
        /// let sqrt = c.sqrt();
        /// assert_eq!(sqrt, (0, 1));
        /// ```
        fn sqrt();
        /// Computes the square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (-1, 0));
        /// // square root of (-1 + 0i) is (0 + i)
        /// c.sqrt_mut();
        /// assert_eq!(c, (0, 1));
        /// ```
        fn sqrt_mut;
        /// Computes the square root, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut c = Complex::with_val(4, (2, 2.25));
        /// // Square root of (2 + 2.25i) is (1.5828 + 0.7108i).
        /// // Nearest with 4 bits of precision: (1.625 + 0.6875i)
        /// let dir = c.sqrt_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1.625, 0.6875));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn sqrt_round;
        /// Computes the square root.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let c = Complex::with_val(53, (2, 2.25));
        /// // Square root of (2 + 2.25i) is (1.5828 + 0.7108i).
        /// let r = c.sqrt_ref();
        /// // Nearest with 4 bits of precision: (1.625 + 0.6875i)
        /// let nearest = (Round::Nearest, Round::Nearest);
        /// let (sqrt, dir) = Complex::with_val_round(4, r, nearest);
        /// assert_eq!(sqrt, (1.625, 0.6875));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn sqrt_ref -> SqrtRef;
    }
    math_op1_no_round! {
        mpc::conj, rraw2;
        /// Computes the complex conjugate.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, 2.5));
        /// let conj = c.conj();
        /// assert_eq!(conj, (1.5, -2.5));
        /// ```
        fn conj();
        /// Computes the complex conjugate.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1.5, 2.5));
        /// c.conj_mut();
        /// assert_eq!(c, (1.5, -2.5));
        /// ```
        fn conj_mut;
        /// Computes the complex conjugate.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
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

    /// Computes the absolute value and returns it as a
    /// [`Float`](struct.Float.html) with the precision of the real
    /// part.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (30, 40));
    /// let f = c.abs();
    /// assert_eq!(f, 50);
    /// ```
    #[inline]
    pub fn abs(self) -> Float {
        let (mut re, im) = self.into_real_imag();
        re.hypot_mut(&im);
        re
    }

    /// Computes the absolute value.
    ///
    /// The real part is set to the absolute value and the imaginary
    /// part is set to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::with_val(53, (30, 40));
    /// c.abs_mut();
    /// assert_eq!(c, (50, 0));
    /// ```
    #[inline]
    pub fn abs_mut(&mut self) {
        let (re, im) = self.as_mut_real_imag();
        re.hypot_mut(im);
        im.assign(Special::Zero);
    }

    /// Computes the absolute value.
    ///
    /// The returned object implements
    /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Float};
    /// let c = Complex::with_val(53, (30, 40));
    /// let f = Float::with_val(53, c.abs_ref());
    /// assert_eq!(f, 50);
    /// ```
    #[inline]
    pub fn abs_ref(&self) -> AbsRef {
        AbsRef { ref_self: self }
    }

    /// Computes the argument, rounding to the nearest.
    ///
    /// The argument is returned as a [`Float`](struct.Float.html)
    /// with the precision of the real part.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (4, 3));
    /// let f = c.arg();
    /// assert_eq!(f, 0.75_f64.atan());
    /// ```
    ///
    /// Special values are handled like atan2 in IEEE 754-2008.
    ///
    /// ```rust
    /// use rug::{Assign, Complex, Float};
    /// use rug::float::Special;
    /// use std::f64;
    /// // f has precision 53, just like f64, so PI constants match.
    /// let mut arg = Float::new(53);
    /// let mut zero = Complex::new(53);
    /// zero.assign((Special::Zero, Special::Zero));
    /// arg.assign(zero.arg_ref());
    /// assert!(arg.is_zero() && arg.is_sign_positive());
    /// zero.assign((Special::Zero, Special::NegZero));
    /// arg.assign(zero.arg_ref());
    /// assert!(arg.is_zero() && arg.is_sign_negative());
    /// zero.assign((Special::NegZero, Special::Zero));
    /// arg.assign(zero.arg_ref());
    /// assert_eq!(arg, f64::consts::PI);
    /// zero.assign((Special::NegZero, Special::NegZero));
    /// arg.assign(zero.arg_ref());
    /// assert_eq!(arg, -f64::consts::PI);
    /// ```
    #[inline]
    pub fn arg(self) -> Float {
        let (mut re, im) = self.into_real_imag();
        unsafe {
            mpfr::atan2(
                re.inner_mut(),
                im.inner(),
                re.inner(),
                rraw(Round::Nearest),
            );
        }
        re
    }

    /// Computes the argument, rounding to the nearest.
    ///
    /// The real part is set to the argument and the imaginary part is
    /// set to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::with_val(53, (40, 30));
    /// c.arg_mut();
    /// assert_eq!(c, (0.75_f64.atan(), 0));
    /// ```
    #[inline]
    pub fn arg_mut(&mut self) {
        self.arg_round(Default::default());
    }

    /// Computes the argument, applying the specified rounding method.
    ///
    /// The real part is set to the argument and the imaginary part is
    /// set to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // use only 4 bits of precision
    /// let mut c = Complex::with_val(4, (3, 4));
    /// // arg(3 + 4i) = 0.9316.
    /// // 0.9316 rounded to the nearest is 0.9375.
    /// let dir = c.arg_round((Round::Nearest, Round::Nearest));
    /// assert_eq!(c, (0.9375, 0));
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Equal));
    /// ```
    #[inline]
    pub fn arg_round(&mut self, round: Round2) -> Ordering2 {
        let (re, im) = self.as_mut_real_imag();
        let ret = unsafe {
            mpfr::atan2(re.inner_mut(), im.inner(), re.inner(), rraw(round.0))
        };
        let dir_re = ordering1(ret);
        let dir_im = im.assign_round(Special::Zero, round.1);
        (dir_re, dir_im)
    }

    /// Computes the argument.
    ///
    /// The returned object implements
    /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Complex, Float};
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
        /// let c = Complex::with_val(53, (13, 24));
        /// let rot1 = c.mul_i(false);
        /// assert_eq!(rot1, (-24, 13));
        /// let rot2 = rot1.mul_i(false);
        /// assert_eq!(rot2, (-13, -24));
        /// let rot2_less1 = rot2.mul_i(true);
        /// assert_eq!(rot2_less1, (-24, 13));
        /// ```
        fn mul_i(negative: bool);
        /// Multiplies the complex number by ±<i>i</i>, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (13, 24));
        /// c.mul_i_mut(false);
        /// assert_eq!(c, (-24, 13));
        /// c.mul_i_mut(false);
        /// assert_eq!(c, (-13, -24));
        /// c.mul_i_mut(true);
        /// assert_eq!(c, (-24, 13));
        /// ```
        fn mul_i_mut;
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
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
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
        /// let c = Complex::with_val(53, (1, 1));
        /// // 1/(1 + i) = (0.5 - 0.5i)
        /// let recip = c.recip();
        /// assert_eq!(recip, (0.5, -0.5));
        /// ```
        fn recip();
        /// Computes the reciprocal, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// // 1/(1 + i) = (0.5 - 0.5i)
        /// c.recip_mut();
        /// assert_eq!(c, (0.5, -0.5));
        /// ```
        fn recip_mut;
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut c = Complex::with_val(4, (1, 2));
        /// // 1/(1 + 2i) = (0.2 - 0.4i), binary (0.00110011..., -0.01100110...)
        /// // 4 bits of precision: (0.001101, -0.01101) = (13/64, -13/32)
        /// let dir = c.recip_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (13.0/64.0, -13.0/32.0));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        /// ```
        fn recip_round;
        /// Computes the reciprocal.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
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

    /// Computes the norm, that is the square of the absolute value,
    /// rounding it to the nearest.
    ///
    /// The norm is returned as a [`Float`](struct.Float.html) with
    /// the precision of the real part.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (3, 4));
    /// let f = c.norm();
    /// assert_eq!(f, 25);
    /// ```
    #[inline]
    pub fn norm(self) -> Float {
        Float::with_val(self.real().prec(), self.norm_ref())
    }

    /// Computes the norm, that is the square of the absolute value,
    /// rounding to the nearest.
    ///
    /// The real part is set to the norm and the imaginary part is set
    /// to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c = Complex::with_val(53, (3, 4));
    /// c.norm_mut();
    /// assert_eq!(c, (25, 0));
    /// ```
    #[inline]
    pub fn norm_mut(&mut self) {
        self.norm_round(Default::default());
    }

    /// Computes the norm, that is the square of the absolute value,
    /// applying the specified rounding method.
    ///
    /// The real part is set to the norm and the imaginary part is set
    /// to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // use only 4 bits of precision
    /// let mut c = Complex::with_val(4, (3, 4));
    /// // 25 rounded up using 4 bits is 26
    /// let dir = c.norm_round((Round::Up, Round::Up));
    /// assert_eq!(c, (26, 0));
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Equal));
    /// ```
    #[inline]
    pub fn norm_round(&mut self, round: Round2) -> Ordering2 {
        let (norm, dir_re) =
            Float::with_val_round(self.real().prec(), self.norm_ref(), round.0);
        let (real, imag) = self.as_mut_real_imag();
        mem::replace(real, norm);
        let dir_im = imag.assign_round(Special::Zero, round.1);
        (dir_re, dir_im)
    }

    /// Computes the norm, that is the square of the absolute value.
    ///
    /// The returned object implements
    /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
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
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, -0.5));
        /// let ln = c.ln();
        /// let expected = Complex::with_val(53, (0.4581, -0.3218));
        /// assert!((ln - expected).abs() < 0.0001);
        /// ```
        fn ln();
        /// Computes the natural logarithm, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1.5, -0.5));
        /// c.ln_mut();
        /// let expected = Complex::with_val(53, (0.4581, -0.3218));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn ln_mut;
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1.5, -0.5));
        /// // ln(1.5 - 0.5i) = (0.4581 - 0.3218i)
        /// // using 4 significant bits: (0.46875 - 0.3125i)
        /// let dir = c.ln_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.46875, -0.3125));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Greater));
        fn ln_round;
        /// Computes the natural logarithm;
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, -0.5));
        /// let ln = Complex::with_val(53, c.ln_ref());
        /// let expected = Complex::with_val(53, (0.4581, -0.3218));
        /// assert!((ln - expected).abs() < 0.0001);
        /// ```
        fn ln_ref -> LnRef;
    }
    math_op1_complex! {
        mpc::log10;
        /// Computes the logarithm to base 10, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, -0.5));
        /// let log10 = c.log10();
        /// let expected = Complex::with_val(53, (0.1990, -0.1397));
        /// assert!((log10 - expected).abs() < 0.0001);
        /// ```
        fn log10();
        /// Computes the logarithm to base 10, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1.5, -0.5));
        /// c.log10_mut();
        /// let expected = Complex::with_val(53, (0.1990, -0.1397));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn log10_mut;
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1.5, -0.5));
        /// // log10(1.5 - 0.5i) = (0.1990 - 0.1397i)
        /// // using 4 significant bits: (0.203125 - 0.140625i)
        /// let dir = c.log10_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.203125, -0.140625));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        fn log10_round;
        /// Computes the logarithm to base 10.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1.5, -0.5));
        /// let log10 = Complex::with_val(53, c.log10_ref());
        /// let expected = Complex::with_val(53, (0.1990, -0.1397));
        /// assert!((log10 - expected).abs() < 0.0001);
        /// ```
        fn log10_ref -> Log10Ref;
    }
    math_op0! {
        /// Generates a root of unity, rounding to the nearest.
        ///
        /// The generated number is the <i>n</i>th root of unity
        /// raised to the power *k*, that is its magnitude is 1 and
        /// its argument is 2<i>πk</i>/<i>n</i>.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let r = Complex::root_of_unity(3, 2);
        /// let c = Complex::with_val(53, r);
        /// let expected = Complex::with_val(53, (-0.5, -0.8660));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn root_of_unity(n: u32, k: u32) -> RootOfUnity;
    }
    math_op1_complex! {
        mpc::exp;
        /// Computes the exponential, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (0.5, -0.75));
        /// let exp = c.exp();
        /// let expected = Complex::with_val(53, (1.2064, -1.1238));
        /// assert!((exp - expected).abs() < 0.0001);
        /// ```
        fn exp();
        /// Computes the exponential, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (0.5, -0.75));
        /// c.exp_mut();
        /// let expected = Complex::with_val(53, (1.2064, -1.1238));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn exp_mut;
        /// Computes the exponential, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (0.5, -0.75));
        /// // exp(0.5 - 0.75i) = (1.2064 - 1.1238i)
        /// // using 4 significant bits: (1.25 - 1.125)
        /// let dir = c.exp_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1.25, -1.125));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        fn exp_round;
        /// Computes the exponential.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (0.5, -0.75));
        /// let exp = Complex::with_val(53, c.exp_ref());
        /// let expected = Complex::with_val(53, (1.2064, -1.1238));
        /// assert!((exp - expected).abs() < 0.0001);
        /// ```
        fn exp_ref -> ExpRef;
    }
    math_op1_complex! {
        mpc::sin;
        /// Computes the sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let sin = c.sin();
        /// let expected = Complex::with_val(53, (1.2985, 0.6350));
        /// assert!((sin - expected).abs() < 0.0001);
        /// ```
        fn sin();
        /// Computes the sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.sin_mut();
        /// let expected = Complex::with_val(53, (1.2985, 0.6350));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn sin_mut;
        /// Computes the sine, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // sin(1 + i) = (1.2985 + 0.6350i)
        /// // using 4 significant bits: (1.25 + 0.625i)
        /// let dir = c.sin_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1.25, 0.625));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Less));
        fn sin_round;
        /// Computes the sine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let sin = Complex::with_val(53, c.sin_ref());
        /// let expected = Complex::with_val(53, (1.2985, 0.6350));
        /// assert!((sin - expected).abs() < 0.0001);
        /// ```
        fn sin_ref -> SinRef;
    }
    math_op1_complex! {
        mpc::cos;
        /// Computes the cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let cos = c.cos();
        /// let expected = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((cos - expected).abs() < 0.0001);
        /// ```
        fn cos();
        /// Computes the cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.cos_mut();
        /// let expected = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn cos_mut;
        /// Computes the cosine, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // cos(1 + i) = (0.8337 - 0.9889i)
        /// // using 4 significant bits: (0.8125 - i)
        /// let dir = c.cos_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.8125, -1));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Less));
        fn cos_round;
        /// Computes the cosine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let cos = Complex::with_val(53, c.cos_ref());
        /// let expected = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((cos - expected).abs() < 0.0001);
        /// ```
        fn cos_ref -> CosRef;
    }
    math_op1_2_complex! {
        mpc::sin_cos;
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine keeps the precision of `self` while the cosine
        /// keeps the precision of `cos`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let (sin, cos) = c.sin_cos(Complex::new(53));
        /// let expected_sin = Complex::with_val(53, (1.2985, 0.6350));
        /// let expected_cos = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((sin - expected_sin).abs() < 0.0001);
        /// assert!((cos - expected_cos).abs() < 0.0001);
        /// ```
        fn sin_cos(cos);
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut sin = Complex::with_val(53, (1, 1));
        /// let mut cos = Complex::new(53);
        /// sin.sin_cos_mut(&mut cos);
        /// let expected_sin = Complex::with_val(53, (1.2985, 0.6350));
        /// let expected_cos = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((sin - expected_sin).abs() < 0.0001);
        /// assert!((cos - expected_cos).abs() < 0.0001);
        /// ```
        fn sin_cos_mut;
        /// Computes the sine and cosine of `self`, applying the
        /// specified rounding methods.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut sin = Complex::with_val(4, (1, 1));
        /// let mut cos = Complex::new(4);
        /// // sin(1 + i) = (1.2985 + 0.6350)
        /// // using 4 significant bits: (1.25 + 0.625i)
        /// // cos(1 + i) = (0.8337 - 0.9889i)
        /// // using 4 significant bits: (0.8125 - i)
        /// let (dir_sin, dir_cos) =
        ///     sin.sin_cos_round(&mut cos, (Round::Nearest, Round::Nearest));
        /// assert_eq!(sin, (1.25, 0.625));
        /// assert_eq!(dir_sin, (Ordering::Less, Ordering::Less));
        /// assert_eq!(cos, (0.8125, -1));
        /// assert_eq!(dir_cos, (Ordering::Less, Ordering::Less));
        /// ```
        fn sin_cos_round;
        /// Computes the sine and cosine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<(&mut Complex, &mut Complex)>`][art].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Complex};
        /// use rug::float::Round;
        /// use rug::ops::AssignRound;
        /// use std::cmp::Ordering;
        /// let phase = Complex::with_val(53, (1, 1));
        /// let sin_cos = phase.sin_cos_ref();
        ///
        /// let (mut sin, mut cos) = (Complex::new(53), Complex::new(53));
        /// (&mut sin, &mut cos).assign(sin_cos);
        /// let expected_sin = Complex::with_val(53, (1.2985, 0.6350));
        /// let expected_cos = Complex::with_val(53, (0.8337, -0.9889));
        /// assert!((sin - expected_sin).abs() < 0.0001);
        /// assert!((cos - expected_cos).abs() < 0.0001);
        ///
        /// // using 4 significant bits: sin = (1.25 + 0.625i)
        /// // using 4 significant bits: cos = (0.8125 - i)
        /// let (mut sin_4, mut cos_4) = (Complex::new(4), Complex::new(4));
        /// let (dir_sin, dir_cos) = (&mut sin_4, &mut cos_4)
        ///     .assign_round(sin_cos, (Round::Nearest, Round::Nearest));
        /// assert_eq!(sin_4, (1.25, 0.625));
        /// assert_eq!(dir_sin, (Ordering::Less, Ordering::Less));
        /// assert_eq!(cos_4, (0.8125, -1));
        /// assert_eq!(dir_cos, (Ordering::Less, Ordering::Less));
        /// ```
        ///
        /// [art]: (../ops/trait.AssignRoundInto.html)
        fn sin_cos_ref -> SinCosRef;
    }
    math_op1_complex! {
        mpc::tan;
        /// Computes the tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let tan = c.tan();
        /// let expected = Complex::with_val(53, (0.2718, 1.0839));
        /// assert!((tan - expected).abs() < 0.0001);
        /// ```
        fn tan();
        /// Computes the tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.tan_mut();
        /// let expected = Complex::with_val(53, (0.2718, 1.0839));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn tan_mut;
        /// Computes the tangent, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // tan(1 + i) = (0.2718 + 1.0839)
        /// // using 4 significant bits: (0.28125 + 1.125i)
        /// let dir = c.tan_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.28125, 1.125));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Greater));
        fn tan_round;
        /// Computes the tangent.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let tan = Complex::with_val(53, c.tan_ref());
        /// let expected = Complex::with_val(53, (0.2718, 1.0839));
        /// assert!((tan - expected).abs() < 0.0001);
        /// ```
        fn tan_ref -> TanRef;
    }
    math_op1_complex! {
        mpc::sinh;
        /// Computes the hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let sinh = c.sinh();
        /// let expected = Complex::with_val(53, (0.6350, 1.2985));
        /// assert!((sinh - expected).abs() < 0.0001);
        /// ```
        fn sinh();
        /// Computes the hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.sinh_mut();
        /// let expected = Complex::with_val(53, (0.6350, 1.2985));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn sinh_mut;
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // sinh(1 + i) = (0.6350 + 1.2985i)
        /// // using 4 significant bits: (0.625 + 1.25i)
        /// let dir = c.sinh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.625, 1.25));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Less));
        fn sinh_round;
        /// Computes the hyperbolic sine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let sinh = Complex::with_val(53, c.sinh_ref());
        /// let expected = Complex::with_val(53, (0.6350, 1.2985));
        /// assert!((sinh - expected).abs() < 0.0001);
        /// ```
        fn sinh_ref -> SinhRef;
    }
    math_op1_complex! {
        mpc::cosh;
        /// Computes the hyperbolic cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let cosh = c.cosh();
        /// let expected = Complex::with_val(53, (0.8337, 0.9889));
        /// assert!((cosh - expected).abs() < 0.0001);
        /// ```
        fn cosh();
        /// Computes the hyperbolic cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.cosh_mut();
        /// let expected = Complex::with_val(53, (0.8337, 0.9889));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn cosh_mut;
        /// Computes the hyperbolic cosine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // cosh(1 + i) = (0.8337 + 0.9889)
        /// // using 4 significant bits: (0.8125 + i)
        /// let dir = c.cosh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.8125, 1));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
        fn cosh_round;
        /// Computes the hyperbolic cosine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let cosh = Complex::with_val(53, c.cosh_ref());
        /// let expected = Complex::with_val(53, (0.8337, 0.9889));
        /// assert!((cosh - expected).abs() < 0.0001);
        /// ```
        fn cosh_ref -> CoshRef;
    }
    math_op1_complex! {
        mpc::tanh;
        /// Computes the hyperbolic tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let tanh = c.tanh();
        /// let expected = Complex::with_val(53, (1.0839, 0.2718));
        /// assert!((tanh - expected).abs() < 0.0001);
        /// ```
        fn tanh();
        /// Computes the hyperbolic tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.tanh_mut();
        /// let expected = Complex::with_val(53, (1.0839, 0.2718));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn tanh_mut;
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // tanh(1 + i) = (1.0839 + 0.2718i)
        /// // using 4 significant bits: (1.125 + 0.28125i)
        /// let dir = c.tanh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1.125, 0.28125));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Greater));
        fn tanh_round;
        /// Computes the hyperbolic tangent.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let tanh = Complex::with_val(53, c.tanh_ref());
        /// let expected = Complex::with_val(53, (1.0839, 0.2718));
        /// assert!((tanh - expected).abs() < 0.0001);
        /// ```
        fn tanh_ref -> TanhRef;
    }
    math_op1_complex! {
        mpc::asin;
        /// Computes the inverse sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let asin = c.asin();
        /// let expected = Complex::with_val(53, (0.6662, 1.0613));
        /// assert!((asin - expected).abs() < 0.0001);
        /// ```
        fn asin();
        /// Computes the inverse sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.asin_mut();
        /// let expected = Complex::with_val(53, (0.6662, 1.0613));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn asin_mut;
        /// Computes the inverse sine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // asin(1 + i) = (0.6662 + 1.0613i)
        /// // using 4 significant bits: (0.6875 + i)
        /// let dir = c.asin_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.6875, 1));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        fn asin_round;
        /// Computes the inverse sine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let asin = Complex::with_val(53, c.asin_ref());
        /// let expected = Complex::with_val(53, (0.6662, 1.0613));
        /// assert!((asin - expected).abs() < 0.0001);
        /// ```
        fn asin_ref -> AsinRef;
    }
    math_op1_complex! {
        mpc::acos;
        /// Computes the inverse cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let acos = c.acos();
        /// let expected = Complex::with_val(53, (0.9046, -1.0613));
        /// assert!((acos - expected).abs() < 0.0001);
        /// ```
        fn acos();
        /// Computes the inverse cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.acos_mut();
        /// let expected = Complex::with_val(53, (0.9046, -1.0613));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn acos_mut;
        /// Computes the inverse cosine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // acos(1 + i) = (0.9046 - 1.0613i)
        /// // using 4 significant bits: (0.875 - i)
        /// let dir = c.acos_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.875, -1));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
        fn acos_round;
        /// Computes the inverse cosine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let acos = Complex::with_val(53, c.acos_ref());
        /// let expected = Complex::with_val(53, (0.9046, -1.0613));
        /// assert!((acos - expected).abs() < 0.0001);
        /// ```
        fn acos_ref -> AcosRef;
    }
    math_op1_complex! {
        mpc::atan;
        /// Computes the inverse tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let atan = c.atan();
        /// let expected = Complex::with_val(53, (1.0172, 0.4024));
        /// assert!((atan - expected).abs() < 0.0001);
        /// ```
        fn atan();
        /// Computes the inverse tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.atan_mut();
        /// let expected = Complex::with_val(53, (1.0172, 0.4024));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn atan_mut;
        /// Computes the inverse tangent, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // atan(1 + i) = (1.0172 + 0.4024i)
        /// // using 4 significant bits: (1 + 0.40625i)
        /// let dir = c.atan_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1, 0.40625));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
        fn atan_round;
        /// Computes the inverse tangent.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let atan = Complex::with_val(53, c.atan_ref());
        /// let expected = Complex::with_val(53, (1.0172, 0.4024));
        /// assert!((atan - expected).abs() < 0.0001);
        /// ```
        fn atan_ref -> AtanRef;
    }
    math_op1_complex! {
        mpc::asinh;
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let asinh = c.asinh();
        /// let expected = Complex::with_val(53, (1.0613, 0.6662));
        /// assert!((asinh - expected).abs() < 0.0001);
        /// ```
        fn asinh();
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.asinh_mut();
        /// let expected = Complex::with_val(53, (1.0613, 0.6662));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn asinh_mut;
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // asinh(1 + i) = (1.0613 + 0.6662i)
        /// // using 4 significant bits: (1 + 0.6875i)
        /// let dir = c.asinh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1, 0.6875));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
        fn asinh_round;
        /// Computes the inverse hyperboic sine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let asinh = Complex::with_val(53, c.asinh_ref());
        /// let expected = Complex::with_val(53, (1.0613, 0.6662));
        /// assert!((asinh - expected).abs() < 0.0001);
        /// ```
        fn asinh_ref -> AsinhRef;
    }
    math_op1_complex! {
        mpc::acosh;
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let acosh = c.acosh();
        /// let expected = Complex::with_val(53, (1.0613, 0.9046));
        /// assert!((acosh - expected).abs() < 0.0001);
        /// ```
        fn acosh();
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.acosh_mut();
        /// let expected = Complex::with_val(53, (1.0613, 0.9046));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn acosh_mut;
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // acosh(1 + i) = (1.0613 + 0.9046i)
        /// // using 4 significant bits: (1 + 0.875i)
        /// let dir = c.acosh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (1, 0.875));
        /// assert_eq!(dir, (Ordering::Less, Ordering::Less));
        fn acosh_round;
        /// Computes the inverse hyperbolic cosine.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let acosh = Complex::with_val(53, c.acosh_ref());
        /// let expected = Complex::with_val(53, (1.0613, 0.9046));
        /// assert!((acosh - expected).abs() < 0.0001);
        /// ```
        fn acosh_ref -> AcoshRef;
    }
    math_op1_complex! {
        mpc::atanh;
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let atanh = c.atanh();
        /// let expected = Complex::with_val(53, (0.4024, 1.0172));
        /// assert!((atanh - expected).abs() < 0.0001);
        /// ```
        fn atanh();
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let mut c = Complex::with_val(53, (1, 1));
        /// c.atanh_mut();
        /// let expected = Complex::with_val(53, (0.4024, 1.0172));
        /// assert!((c - expected).abs() < 0.0001);
        /// ```
        fn atanh_mut;
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut c = Complex::with_val(4, (1, 1));
        /// // atanh(1 + i) = (0.4024 + 1.0172i)
        /// // using 4 significant bits: (0.40625 + i)
        /// let dir = c.atanh_round((Round::Nearest, Round::Nearest));
        /// assert_eq!(c, (0.40625, 1));
        /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
        fn atanh_round;
        /// Computes the inverse hyperbolic tangent.
        ///
        /// The returned object implements
        /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Complex;
        /// let c = Complex::with_val(53, (1, 1));
        /// let atanh = Complex::with_val(53, c.atanh_ref());
        /// let expected = Complex::with_val(53, (0.4024, 1.0172));
        /// assert!((atanh - expected).abs() < 0.0001);
        /// ```
        fn atanh_ref -> AtanhRef;
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range 0 ≤ *x* < 1.
    ///
    /// This is equivalent to generating a random integer in the range
    /// 0 ≤ *x* < 2<sup>*p*</sup> for each part, where 2<sup>*p*</sup>
    /// is two raised to the power of the precision, and then dividing
    /// the integer by 2<sup>*p*</sup>. The smallest non-zero result
    /// will thus be 2<sup>−<i>p</i></sup>, and will only have one bit
    /// set. In the smaller possible results, many bits will be zero,
    /// and not all the precision will be used.
    ///
    /// The returned object implements
    /// [`AssignInto<Result<&mut Complex, &mut Complex>`][at].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Complex};
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut c = Ok(Complex::new(2));
    /// c.assign(Complex::random_bits(&mut rand));
    /// let c = c.unwrap();
    /// let (re, im) = c.into_real_imag();
    /// assert!(re == 0.0 || re == 0.25 || re == 0.5 || re == 0.75);
    /// assert!(im == 0.0 || im == 0.25 || im == 0.5 || im == 0.75);
    /// println!("0.0 ≤ {} < 1.0", re);
    /// println!("0.0 ≤ {} < 1.0", im);
    /// ```
    ///
    /// # Errors
    ///
    /// In all the normal cases, the result will be exact. However, if
    /// the precision is very large, and the generated random number
    /// is very small, this may require an exponent smaller than
    /// [`float::exp_min()`](float/fn.exp_min.html); in this case, the
    /// number is set to Nan and an error is returned. This would most
    /// likely be a programming error.
    ///
    /// [at]: (../ops/trait.AssignInto.html)
    #[inline]
    pub fn random_bits<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomBits<'a, 'b> {
        RandomBits { rng }
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range 0 ≤ *x* < 1.
    ///
    /// This method is deprecated. The code
    ///
    /// ```rust
    /// use rug::Complex;
    /// let mut c: Complex;
    /// // ...
    /// # c = Complex::new(53);
    /// # let mut rand = ::rug::rand::RandState::new();
    /// # let rng = &mut rand;
    /// # #[allow(deprecated)]
    /// match c.assign_random_bits(rng) {
    ///     Ok(()) => { /* ok */ }
    ///     Err(()) => { /* error */ }
    /// }
    /// ```
    ///
    /// can be replaced with
    ///
    /// ```rust
    /// use rug::{Assign, Complex};
    /// let mut c: Complex;
    /// // ...
    /// # c = Complex::new(53);
    /// # let mut rand = ::rug::rand::RandState::new();
    /// # let rng = &mut rand;
    /// let mut result = Ok(&mut c);
    /// result.assign(Complex::random_bits(rng));
    /// match result {
    ///     Ok(_) => { /* ok */ }
    ///     Err(_) => { /* error */ }
    /// };
    /// ```
    #[deprecated(since = "0.9.2",
                 note = "use `random_bits` instead; see documentation for an \
                         example replacement.")]
    #[inline]
    pub fn assign_random_bits(
        &mut self,
        rng: &mut RandState,
    ) -> Result<(), ()> {
        let mut r = Ok(self);
        Complex::random_bits(rng).assign_into(&mut r);
        match r {
            Ok(_) => Ok(()),
            Err(_) => Err(()),
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the continous range 0 ≤ *x* < 1, and rounds
    /// to the nearest.
    ///
    /// The result parts can be rounded up to be equal to one. Unlike
    /// the [`assign_random_bits`](#method.assign_random_bits) method
    /// which generates a discrete random number at intervals
    /// depending on the precision, this method is equivalent to
    /// generating a continuous random number with infinite precision
    /// and then rounding the result. This means that even the smaller
    /// numbers will be using all the available precision bits, and
    /// rounding is performed in all cases, not in some corner case.
    ///
    /// Rounding directions for generated random numbers cannot be
    /// `Ordering::Equal`, as the random numbers generated can be
    /// considered to have infinite precision before rounding.
    ///
    /// The returned object implements
    /// [`AssignRoundInto<Complex>`](../ops/trait.AssignRoundInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let c = Complex::with_val(2, Complex::random_cont(&mut rand));
    /// let (re, im) = c.into_real_imag();
    /// // The significand is either 0b10 or 0b11
    /// //           10           11
    /// assert!(re == 1.0 || re == 0.75 ||
    ///         re == 0.5 || re == 0.375 ||
    ///         re == 0.25 || re <= 0.1875);
    /// assert!(im == 1.0 || im == 0.75 ||
    ///         im == 0.5 || im == 0.375 ||
    ///         im == 0.25 || im <= 0.1875);
    /// ```
    #[inline]
    pub fn random_cont<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomCont<'a, 'b> {
        RandomCont { rng }
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the continous range 0 ≤ *x* < 1, and rounds
    /// to the nearest.
    #[deprecated(since = "0.9.2",
                 note = "use `random_cont` instead; \
                         `c.assign_random_cont(rng)` can be replaced with \
                         `c.assign(Complex::random_cont(rng))`.")]
    #[inline]
    pub fn assign_random_cont(&mut self, rng: &mut RandState) {
        Complex::random_cont(rng).assign_round_into(self, Default::default());
    }

    #[cfg(feature = "rand")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the continous range 0 ≤ *x* < 1, and
    /// applies the specified rounding method.
    #[deprecated(since = "0.9.2",
                 note = "use `random_cont` instead; \
                         `c.assign_random_cont_round(rng, round)` can be \
                         replaced with \
                         `c.assign_round(Complex::random_cont(rng, round))`.")]
    #[inline]
    pub fn assign_random_cont_round(
        &mut self,
        rng: &mut RandState,
        round: Round2,
    ) -> Ordering2 {
        Complex::random_cont(rng).assign_round_into(self, round)
    }
}

ref_math_op1_complex! { mpc::proj; struct ProjRef {} }
ref_math_op1_complex! { mpc::sqr; struct SquareRef {} }
ref_math_op1_complex! { mpc::sqrt; struct SqrtRef {} }
ref_math_op1_complex! { mpc::conj; struct ConjugateRef {} }

#[derive(Clone, Copy)]
pub struct AbsRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRoundInto<Float> for AbsRef<'a> {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round_into(self, dst: &mut Float, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::abs(dst.inner_mut(), self.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

#[derive(Clone, Copy)]
pub struct ArgRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRoundInto<Float> for ArgRef<'a> {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round_into(self, dst: &mut Float, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::arg(dst.inner_mut(), self.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

ref_math_op1_complex! { xmpc::mul_i; struct MulIRef { negative: bool } }
ref_math_op1_complex! { xmpc::recip; struct RecipRef {} }

#[derive(Clone, Copy)]
pub struct NormRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRoundInto<Float> for NormRef<'a> {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round_into(self, dst: &mut Float, round: Round) -> Ordering {
        let ret = unsafe {
            mpc::norm(dst.inner_mut(), self.ref_self.inner(), rraw(round))
        };
        ret.cmp(&0)
    }
}

ref_math_op1_complex! { mpc::log; struct LnRef {} }
ref_math_op1_complex! { mpc::log10; struct Log10Ref {} }
ref_math_op0_complex! {
    mpc::rootofunity; struct RootOfUnity { n: u32, k: u32 }
}
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

#[cfg(feature = "rand")]
pub struct RandomBits<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b, 'c: 'b> AssignInto<Result<&'a mut Complex, &'a mut Complex>>
    for RandomBits<'b, 'c> {
    #[inline]
    fn assign_into(self, dst: &mut Result<&'a mut Complex, &'a mut Complex>) {
        let err = match *dst {
            Ok(ref mut dest) | Err(ref mut dest) => {
                let (real, imag) = dest.as_mut_real_imag();
                let (mut rreal, mut rimag) = (Ok(real), Ok(imag));
                Float::random_bits(self.rng).assign_into(&mut rreal);
                Float::random_bits(self.rng).assign_into(&mut rimag);
                rreal.is_err() || rimag.is_err()
            }
        };
        if err != dst.is_err() {
            misc::result_swap(dst)
        }
    }
}

#[cfg(feature = "rand")]
pub struct RandomCont<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignRoundInto<Complex> for RandomCont<'a, 'b> {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        let (real, imag) = dst.as_mut_real_imag();
        (
            Float::random_cont(self.rng).assign_round_into(real, round.0),
            Float::random_cont(self.rng).assign_round_into(imag, round.1),
        )
    }
}

#[derive(Clone, Copy)]
pub struct BorrowComplex<'a> {
    inner: mpc_t,
    phantom: PhantomData<&'a Complex>,
}

impl<'a> Deref for BorrowComplex<'a> {
    type Target = Complex;
    #[inline]
    fn deref(&self) -> &Complex {
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

pub fn append_to_string(
    s: &mut String,
    c: &Complex,
    radix: i32,
    precision: Option<usize>,
    round: Round2,
    to_upper: bool,
    sign_plus: bool,
    prefix: &str,
) {
    let (re, im) = c.as_real_imag();
    let re_plus = sign_plus && re.is_sign_positive();
    let im_plus = sign_plus && im.is_sign_positive();
    let re_prefix = !prefix.is_empty() && (re.is_finite() || re.is_zero());
    let im_prefix = !prefix.is_empty() && (im.is_finite() || im.is_zero());
    // To avoid reallocations in append_to_string, add 3 for "( )".
    // There is no need for space for a nul terminator, as it will not
    // be there at the same time as ')'.
    let mut additional = 3;
    additional += if re_plus { 1 } else { 0 };
    additional += if im_plus { 1 } else { 0 };
    additional += if re_prefix { prefix.len() } else { 0 };
    additional += if im_prefix { prefix.len() } else { 0 };
    additional = big_float::req_chars(re, radix, precision, additional);
    additional = big_float::req_chars(im, radix, precision, additional);
    s.reserve(additional);
    s.push('(');
    if re_plus {
        s.push('+');
    }
    let prefix_start = s.len();
    if re_prefix {
        s.push_str(prefix);
    }
    let prefix_end = s.len();
    big_float::append_to_string(s, re, radix, precision, round.0, to_upper);
    if re_prefix && s.as_bytes()[prefix_end] == b'-' {
        unsafe {
            let bytes =
                slice::from_raw_parts_mut(s.as_ptr() as *mut _, s.len());
            bytes[prefix_start] = b'-';
            bytes[prefix_start + 1..prefix_end + 1]
                .copy_from_slice(prefix.as_bytes());
        }
    }
    s.push(' ');
    if im_plus {
        s.push('+');
    }
    let prefix_start = s.len();
    if im_prefix {
        s.push_str(prefix);
    }
    let prefix_end = s.len();
    big_float::append_to_string(s, im, radix, precision, round.1, to_upper);
    if im_prefix && s.as_bytes()[prefix_end] == b'-' {
        unsafe {
            let bytes =
                slice::from_raw_parts_mut(s.as_ptr() as *mut _, s.len());
            bytes[prefix_start] = b'-';
            bytes[prefix_start + 1..prefix_end + 1]
                .copy_from_slice(prefix.as_bytes());
        }
    }
    s.push(')');
}

/// A validated string that can always be converted to a `Complex`.
///
/// See the [`Complex::valid_str_radix`][valid] method.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// use rug::complex::ValidComplex;
/// // This string is correct in radix 10, it cannot fail.
/// let s = "(1.25e-1 2.37e+2)";
/// let valid: ValidComplex = match Complex::valid_str_radix(s, 10) {
///     Ok(valid) => valid,
///     Err(_) => unreachable!(),
/// };
/// let c = Complex::with_val(53, valid);
/// assert_eq!(c, (0.125, 237));
/// ```
///
/// [valid]: ../struct.Complex.html#method.valid_str_radix
#[derive(Clone, Debug)]
pub struct ValidComplex<'a> {
    poss: ValidPoss<'a>,
}

#[derive(Clone, Debug)]
enum ValidPoss<'a> {
    Real(ValidFloat<'a>),
    Complex(ValidFloat<'a>, ValidFloat<'a>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing a `Complex` number.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// use rug::complex::ParseComplexError;
/// // This string is not a complex number.
/// let s = "something completely different (_!_!_)";
/// let error: ParseComplexError = match Complex::valid_str_radix(s, 4) {
///     Ok(_) => unreachable!(),
///     Err(error) => error,
/// };
/// println!("Parse error: {:?}", error);
/// ```
pub struct ParseComplexError {
    kind: ParseErrorKind,
}

impl<'a> AssignRoundInto<Complex> for ValidComplex<'a> {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        match self.poss {
            ValidPoss::Real(re) => {
                let real_ord = dst.mut_real().assign_round(re, round.0);
                dst.mut_imag().assign(Special::Zero);
                (real_ord, Ordering::Equal)
            }
            ValidPoss::Complex(re, im) => {
                let real_ord = dst.mut_real().assign_round(re, round.0);
                let imag_ord = dst.mut_imag().assign_round(im, round.1);
                (real_ord, imag_ord)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[inline]
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

#[inline]
pub fn rraw2(round: Round2) -> mpc::rnd_t {
    #[allow(deprecated)]
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
        (Round::AwayFromZero, _) | (_, Round::AwayFromZero) => unimplemented!(),
    }
}

#[inline]
fn ordering1(ord: c_int) -> Ordering {
    ord.cmp(&0)
}

#[inline]
pub fn ordering2(ord: c_int) -> Ordering2 {
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
