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

use {AddRound, AssignRound, Constant, DivRound, Float, FromRound, MulRound,
     ParseFloatError, PowRound, Round, ShlRound, ShrRound, Special, SubRound,
     ValidFloat};
use {Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign, PowFromAssign,
     SubFromAssign};
use Rational;
use complex::xmpc;
use float;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpc::{self, mpc_t};
use gmp_mpfr_sys::mpfr;
#[cfg(feature = "random")]
use rand::Rng;
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

type Round2 = (Round, Round);
const NEAREST: Round2 = (Round::Nearest, Round::Nearest);

/// The `Prec` trait is used to specify the precision of the real and
/// imaginary parts of a `Complex` number.
pub trait Prec {
    /// Returs the precision for the real and imaginary parts.
    fn prec(self) -> (u32, u32);
}

impl Prec for u32 {
    fn prec(self) -> (u32, u32) {
        (self, self)
    }
}

impl Prec for (u32, u32) {
    fn prec(self) -> (u32, u32) {
        self
    }
}

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
    inner: mpc_t,
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

impl Drop for Complex {
    fn drop(&mut self) {
        unsafe {
            mpc::clear(self.inner_mut());
        }
    }
}

macro_rules! math_op1 {
    {
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $($param: $T,)*
        ) -> &mut Complex {
            self.$method_round($($param,)* NEAREST);
            self
        }

        $(#[$attr_round])*
        pub fn $method_round(
            &mut self,
            $($param: $T,)*
            round: Round2,
        ) -> Ordering2 {
            let mpc_ret = unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    rraw2(round),
                )
            };
            ordering2(mpc_ret)
        }

        $(#[$attr_ref])*
        pub fn $method_ref(&self $(, $param: $T)*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! ref_math_op1 {
    {
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a Complex,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Ref<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
                round: Round2,
            ) -> Ordering2 {
                let mpc_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                        rraw2(round),
                    )
                };
                ordering2(mpc_ret)
            }
        }
    };
}

macro_rules! math_op1_2 {
    {
        $(#[$attr:meta])*
        fn $method:ident($rop:ident $(, $param:ident: $T:ty)*);
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $rop: &mut Complex,
            $($param: $T,)*
        ) {
            self.$method_round(
                $rop,
                $($param,)*
                NEAREST,
            );
        }

        $(#[$attr_round])*
        pub fn $method_round(
            &mut self,
            $rop: &mut Complex,
            $($param: $T,)*
            round: Round2,
        ) -> (Ordering2, Ordering2) {
            let mpc_ret = unsafe {
                $func(
                    self.inner_mut(),
                    $rop.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                    rraw2(round),
                    rraw2(round),
                )
            };
            (ordering2(mpc::INEX1(mpc_ret)), ordering2(mpc::INEX2(mpc_ret)))
        }

        $(#[$attr_ref])*
        pub fn $method_ref(
            &self,
            $($param: $T,)*
        ) -> $Ref {
            $Ref {
                ref_self: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! ref_math_op1_2 {
    {
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a Complex,
            $($param: $T,)*
        }

        impl<'a> Assign<$Ref<'a>> for (&'a mut Complex, &'a mut Complex) {
            fn assign(&mut self, src: $Ref<'a>) {
                self.assign_round(src, NEAREST);
            }
        }

        impl<'a> AssignRound<$Ref<'a>> for (&'a mut Complex, &'a mut Complex) {
            type Round = Round2;
            type Ordering = (Ordering2, Ordering2);
            fn assign_round(
                &mut self,
                src: $Ref<'a>,
                round: Round2,
            ) -> (Ordering2, Ordering2) {
                let mpc_ret = unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                        rraw2(round),
                        rraw2(round),
                    )
                };
                (ordering2(mpc::INEX1(mpc_ret)), ordering2(mpc::INEX2(mpc_ret)))
            }
        }
    };
}

impl Complex {
    /// Create a new complex number with the specified precisions for
    /// the real and imaginary parts and with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let r1 = Complex::new(32);
    /// assert_eq!(r1.prec(), (32, 32));
    /// let r2 = Complex::new((32, 64));
    /// assert_eq!(r2.prec(), (32, 64));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    pub fn new<P: Prec>(prec: P) -> Complex {
        let p = prec.prec();
        assert!(
            p.0 >= float::prec_min() && p.0 <= float::prec_max() &&
                p.1 >= float::prec_min() &&
                p.1 <= float::prec_max(),
            "precision out of range"
        );
        unsafe {
            let mut inner: mpc_t = mem::uninitialized();
            mpc::init3(&mut inner, p.0 as mpfr::prec_t, p.1 as mpfr::prec_t);
            let real = mpc::realref(&mut inner);
            let imag = mpc::imagref(&mut inner);
            mpfr::set_zero(real, 0);
            mpfr::set_zero(imag, 0);
            Complex { inner: inner }
        }
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
    /// let mut r = Complex::from(((4.875, 4.625), 6));
    /// assert_eq!(r, (4.875, 4.625));
    /// r.set_prec(4);
    /// assert_eq!(r, (5.0, 4.5));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    pub fn set_prec<P: Prec>(&mut self, prec: P) {
        self.set_prec_round(prec, NEAREST);
    }

    /// Sets the precision of the real and imaginary parts, applying
    /// the specified rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// use std::cmp::Ordering;
    /// let mut r = Complex::from(((4.875, 4.625), 6));
    /// assert_eq!(r, (4.875, 4.625));
    /// let dir = r.set_prec_round(4, (Round::Down, Round::Up));
    /// assert_eq!(r, (4.5, 5.0));
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the precision is out of the allowed range.
    pub fn set_prec_round<P: Prec>(
        &mut self,
        prec: P,
        round: Round2,
    ) -> Ordering2 {
        let p = prec.prec();
        let (real, imag) = self.as_mut_real_imag();
        (real.set_prec_round(p.0, round.0), imag.set_prec_round(p.1, round.1))
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
    pub fn from_str<P: Prec>(
        src: &str,
        prec: P,
    ) -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new(prec);
        val.assign_str(src)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified precision,
    /// applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// use std::cmp::Ordering;
    /// let round = (Round::Down, Round::Up);
    /// let res = Complex::from_str_round("(14.1 14.2)", 4, round);
    /// let (c, dir) = res.unwrap();
    /// assert_eq!(*c.real(), 14);
    /// assert_eq!(*c.imag(), 15);
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
    pub fn from_str_round<P: Prec>
        (
        src: &str,
        prec: P,
        round: Round2,
    ) -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new(prec);
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
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix<P: Prec>(
        src: &str,
        radix: i32,
        prec: P,
    ) -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new(prec);
        val.assign_str_radix(src, radix)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// use std::cmp::Ordering;
    /// let round = (Round::Nearest, Round::Nearest);
    /// let res = Complex::from_str_radix_round("(c.c c.1)", 16, 4, round);
    /// let (c, dir) = res.unwrap();
    /// assert_eq!(*c.real(), 13);
    /// assert_eq!(*c.imag(), 12);
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix_round<P: Prec>
        (
        src: &str,
        radix: i32,
        prec: P,
        round: Round2,
    ) -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new(prec);
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
    /// let c1 = Complex::from((valid1.unwrap(), 53));
    /// assert_eq!(c1, (0.25 * (1.0 + 0.25 * 2.0), 4.0 * (3.0 + 4.0 * 2.0)));
    /// let valid2 = Complex::valid_str_radix("(12 yz)", 36);
    /// let c2 = Complex::from((valid2.unwrap(), 53));
    /// assert_eq!(c2, (2.0 + 36.0 * 1.0, 35.0 + 36.0 * 34.0));
    ///
    /// let invalid = Complex::valid_str_radix("(0, 0)", 3);
    /// let invalid_f = Complex::from_str_radix("(0, 0)", 3, 53);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
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
            let space =
                src.find(' ').ok_or(Error { kind: Kind::MissingSpace })?;
            let real_str = &src[1..space];
            let re =
                Float::valid_str_radix(real_str, radix)
                    .map_err(|e| Error { kind: Kind::InvalidRealFloat(e) })?;
            let rest = &src[space + 1..];
            let close = rest.find(')')
                .ok_or(Error { kind: Kind::MissingClose })?;
            let imag_str = &rest[0..close];
            let im =
                Float::valid_str_radix(imag_str, radix)
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

    /// Returns a string representation of `self` for the specified
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
    /// let c1 = Complex::from((0, 53));
    /// assert_eq!(c1.to_string_radix(10, None), "(0.0 0.0)");
    /// let c2 = Complex::from(((15, 5), 12));
    /// assert_eq!(c2.to_string_radix(16, None), "(f.000@0 5.000@0)");
    /// let c3 = Complex::from(((10, -4), 53));
    /// assert_eq!(c3.to_string_radix(10, Some(3)), "(1.00e1 -4.00e0)");
    /// assert_eq!(c3.to_string_radix(5, Some(3)), "(2.00e1 -4.00e0)");
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
        self.to_string_radix_round(radix, num_digits, NEAREST)
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` applying the specified rounding method.
    ///
    /// The exponent is encoded in decimal. If the number of digits is
    /// not specified, the output string will have enough precision
    /// such that reading it again will give the exact same number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// let c = Complex::from((10.4, 10));
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
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseComplexError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Complex` number from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// use std::cmp::Ordering;
    /// let mut c = Complex::new((4, 4));
    /// let round = (Round::Down, Round::Up);
    /// let dir = c.assign_str_round("(14.1 14.2)", round).unwrap();
    /// assert_eq!(*c.real(), 14);
    /// assert_eq!(*c.imag(), 15);
    /// assert_eq!(dir, (Ordering::Less, Ordering::Greater));
    /// ```
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
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseComplexError> {
        self.assign_str_radix_round(src, radix, NEAREST).map(|_| ())
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::{Complex, Round};
    /// use std::cmp::Ordering;
    /// let mut c = Complex::new((4, 4));
    /// let round = (Round::Nearest, Round::Nearest);
    /// let dir = c.assign_str_radix_round("(c.c c.1)", 16, round).unwrap();
    /// assert_eq!(*c.real(), 13);
    /// assert_eq!(*c.imag(), 12);
    /// assert_eq!(dir, (Ordering::Greater, Ordering::Less));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix_round(
        &mut self,
        src: &str,
        radix: i32,
        round: Round2,
    ) -> Result<Ordering2, ParseComplexError> {
        Ok(self.assign_round(Complex::valid_str_radix(src, radix)?, round))
    }

    /// Borrows the real part as a `Float`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::from(((12.5, -20.75), 53));
    /// assert_eq!(*c.real(), 12.5)
    /// ```
    pub fn real(&self) -> &Float {
        unsafe {
            let ptr = mpc::realref_const(self.inner());
            &*(ptr as *const Float)
        }
    }

    /// Borrows the imaginary part as a `Float`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::from(((12.5, -20.75), 53));
    /// assert_eq!(*c.imag(), -20.75)
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
    /// let mut c = Complex::from(((12.5, -20.75), 53));
    /// assert_eq!(c, (12.5, -20.75));
    /// *c.mut_real() /= 2;
    /// assert_eq!(c, (6.25, -20.75));
    /// ```
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
    /// let mut c = Complex::from(((12.5, -20.75), 53));
    /// assert_eq!(c, (12.5, -20.75));
    /// *c.mut_imag() *= 4;
    /// assert_eq!(c, (12.5, -83));
    /// ```
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
    /// let c = Complex::from(((12.5, -20.75), 53));
    /// assert_eq!(c, (12.5, -20.75));
    /// let (re, im) = c.as_real_imag();
    /// assert_eq!(*re, 12.5);
    /// assert_eq!(*im, -20.75);
    /// ```
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
    /// let mut c = Complex::from(((12.5, -20.75), 53));
    /// {
    ///     let (real, imag) = c.as_mut_real_imag();
    ///     *real /= 2;
    ///     *imag *= 4;
    ///     // borrow ends here
    /// }
    /// assert_eq!(c, (6.25, -83));
    /// ```
    pub fn as_mut_real_imag(&mut self) -> (&mut Float, &mut Float) {
        unsafe {
            let real_ptr = mpc::realref(self.inner_mut());
            let imag_ptr = mpc::imagref(self.inner_mut());
            (&mut *(real_ptr as *mut Float), &mut *(imag_ptr as *mut Float))
        }
    }

    /// Converts `self` into real and imaginary `Float` values,
    /// consuming `self`.
    ///
    /// This function reuses the allocated memory and does not
    /// allocate any new memory.
    ///
    /// ```rust
    /// use rug::Complex;
    /// let c = Complex::from(((12.5, -20.75), 53));
    /// let (real, imag) = c.into_real_imag();
    /// assert_eq!(real, 12.5);
    /// assert_eq!(imag, -20.75);
    /// ```
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

    math_op1! {
        /// Computes a projection onto the Riemann sphere, rounding to
        /// the nearest.
        fn proj();
        /// Computes a projection onto the Riemann sphere, applying
        /// the specified rounding method.
        fn proj_round;
        /// Computes the projection onto the Riemann
        /// sphere.
        fn proj_ref -> ProjRef;
        mpc::proj
    }
    math_op1! {
        /// Computes the square, rounding to the nearest.
        fn square();
        /// Computes the square, applying the specified rounding method.
        fn square_round;
        /// Computes the square.
        fn square_ref -> SquareRef;
        mpc::sqr
    }
    math_op1! {
        /// Computes the square root, rounding to the nearest.
        fn sqrt();
        /// Computes the square root, applying the specified rounding
        /// method.
        fn sqrt_round;
        /// Computes the square root.
        fn sqrt_ref -> SqrtRef;
        mpc::sqrt
    }
    math_op1! {
        /// Computes the complex conjugate, rounding to the nearest.
        fn conjugate();
        /// Computes the complex conjugate, applying the specified
        /// rounding method.
        fn conjugate_round;
        /// Computes the complex conjugate.
        fn conjugate_ref -> ConjugateRef;
        mpc::conj
    }

    /// Computes the absolute value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Complex, Float, Special};
    ///
    /// let c1 = Complex::from(((30, 40), 53));
    /// assert_eq!(Float::from((c1.abs_ref(), 53)), 50);
    /// let c2 = Complex::from(((12, Special::Infinity), 53));
    /// assert!(Float::from((c2.abs_ref(), 53)).is_infinite());
    /// ```
    pub fn abs_ref(&self) -> AbsRef {
        AbsRef { ref_self: self }
    }

    /// Computes the argument.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Complex, Float, Special};
    /// use std::f64;
    /// // f has precision 53, just like f64, so PI constants match.
    /// let mut arg = Float::new(53);
    /// let c_pos = Complex::from((1, 53));
    /// arg.assign(c_pos.arg_ref());
    /// assert!(arg.is_zero());
    /// let c_neg = Complex::from((-1.3, 53));
    /// arg.assign(c_neg.arg_ref());
    /// assert_eq!(arg, f64::consts::PI);
    /// let c_pi_4 = Complex::from(((1.333, 1.333), 53));
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
    pub fn arg_ref(&self) -> ArgRef {
        ArgRef { ref_self: self }
    }

    math_op1! {
        /// Multiplies the complex number by *i*, rounding to the nearest.
        fn mul_i(negative: bool);
        /// Multiplies the complex number by *i*, applying the specified
        /// rounding method.
        fn mul_i_round;
        /// Multiplies the complex number by *i*.
        fn mul_i_ref -> MulIRef;
        xmpc::mul_i
    }
    math_op1! {
        /// Computes the reciprocal, rounding to the nearest.
        fn recip();
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        fn recip_round;
        /// Computes the reciprocal.
        fn recip_ref -> RecipRef;
        xmpc::recip
    }

    /// Computes the norm, that is the square of the absolute value.
    pub fn norm_ref(&self) -> NormRef {
        NormRef { ref_self: self }
    }

    math_op1! {
        /// Computes the natural logarithm, rounding to the nearest.
        fn ln();
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        fn ln_round;
        /// Computes the natural logarithm;
        fn ln_ref -> LnRef;
        mpc::log
    }
    math_op1! {
        /// Computes the logarithm to base 10, rounding to the nearest.
        fn log10();
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        fn log10_round;
        /// Computes the logarithm to base 10.
        fn log10_ref -> Log10Ref;
        mpc::log10
    }
    math_op1! {
        /// Computes the exponential, rounding to the nearest.
        fn exp();
        /// Computes the exponential, applying the specified rounding
        /// method.
        fn exp_round;
        /// Computes the exponential.
        fn exp_ref -> ExpRef;
        mpc::exp
    }
    math_op1! {
        /// Computes the sine, rounding to the nearest.
        fn sin();
        /// Computes the sine, applying the specified rounding method.
        fn sin_round;
        /// Computes the sine.
        fn sin_ref -> SinRef;
        mpc::sin
    }
    math_op1! {
        /// Computes the cosine, rounding to the nearest.
        fn cos();
        /// Computes the cosine, applying the specified rounding method.
        fn cos_round;
        /// Computes the cosine.
        fn cos_ref -> CosRef;
        mpc::cos
    }
    math_op1_2! {
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
        /// let angle = Complex::from(((0.5, 0.2), 53));
        /// let r = angle.sin_cos_ref();
        /// // use only 10 bits of precision here to
        /// // make comparison easier
        /// let (mut sin, mut cos) = (Complex::new(10), Complex::new(10));
        /// (&mut sin, &mut cos).assign(r);
        /// assert_eq!(sin, Complex::from(((0.48905, 0.17669), 10)));
        /// assert_eq!(cos, Complex::from(((0.89519, -0.096526), 10)));
        fn sin_cos_ref -> SinCosRef;
        mpc::sin_cos
    }
    math_op1! {
        /// Computes the tangent, rounding to the nearest.
        fn tan();
        /// Computes the tangent, applying the specified rounding method.
        fn tan_round;
        /// Computes the tangent.
        fn tan_ref -> TanRef;
        mpc::tan
    }
    math_op1! {
        /// Computes the hyperbolic sine, rounding to the nearest.
        fn sinh();
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        fn sinh_round;
        /// Computes the hyperbolic sine.
        fn sinh_ref -> SinhRef;
        mpc::sinh
    }
    math_op1! {
        /// Computes the hyperbolic cosine, rounding to the nearest.
        fn cosh();
        /// Computes the hyperbolic cosine, applying the specified rounding
        /// method.
        fn cosh_round;
        /// Computes the hyperbolic cosine.
        fn cosh_ref -> CoshRef;
        mpc::cosh
    }
    math_op1! {
        /// Computes the hyperbolic tangent, rounding to the nearest.
        fn tanh();
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        fn tanh_round;
        /// Computes the hyperbolic tangent.
        fn tanh_ref -> TanhRef;
        mpc::tanh
    }
    math_op1! {
        /// Computes the inverse sine, rounding to the nearest.
        fn asin();
        /// Computes the inverse sine, applying the specified rounding
        /// method.
        fn asin_round;
        /// Computes the inverse sine.
        fn asin_ref -> AsinRef;
        mpc::asin
    }
    math_op1! {
        /// Computes the inverse cosine, rounding to the nearest.
        fn acos();
        /// Computes the inverse cosine, applying the specified rounding
        /// method.
        fn acos_round;
        /// Computes the inverse cosine.
        fn acos_ref -> AcosRef;
        mpc::acos
    }
    math_op1! {
        /// Computes the inverse tangent, rounding to the nearest.
        fn atan();
        /// Computes the inverse tangent, applying the specified rounding
        /// method.
        fn atan_round;
        /// Computes the inverse tangent.
        fn atan_ref -> AtanRef;
        mpc::atan
    }
    math_op1! {
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        fn asinh();
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        fn asinh_round;
        /// Computes the inverse hyperboic sine.
        fn asinh_ref -> AsinhRef;
        mpc::asinh
    }
    math_op1! {
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        fn acosh();
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        fn acosh_round;
        /// Computes the inverse hyperbolic cosine.
        fn acosh_ref -> AcoshRef;
        mpc::acosh
    }
    math_op1! {
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        fn atanh();
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        fn atanh_round;
        /// Computes the inverse hyperbolic tangent.
        fn atanh_ref -> AtanhRef;
        mpc::atanh
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_bits_round).
    pub fn assign_random_bits<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_bits_round(rng, NEAREST);
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, round.0)`]
    /// (../rugflo/struct.Float.html#method.assign_random_bits_round)
    /// on the real part, and the same with `round.1` on the
    /// imaginary part.
    pub fn assign_random_bits_round<R: Rng>(
        &mut self,
        rng: &mut R,
        round: Round2,
    ) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_bits_round(rng, round.0),
         imag.assign_random_bits_round(rng, round.1))
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number, rounding to the nearest.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_cont_round).
    pub fn assign_random_cont<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_cont_round(rng, NEAREST);
    }

    #[cfg(feature = "random")]
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
    pub fn assign_random_cont_round<R: Rng>(
        &mut self,
        rng: &mut R,
        round: Round2,
    ) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_cont_round(rng, round.0),
         imag.assign_random_cont_round(rng, round.1))
    }
}


impl From<(Float, Float)> for Complex {
    /// Constructs a `Complex` number from a real `Float` and
    /// imaginary `Float`.
    ///
    /// This constructor does not allocate, as it reuses the `Float`
    /// components.
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

impl<T, P: Prec> From<(T, P)> for Complex
where
    Complex: FromRound<T,
                       P,
                       Round = Round2>,
{
    fn from((t, prec): (T, P)) -> Complex {
        Complex::from_round(t, prec, NEAREST).0
    }
}

impl<T, P: Prec> FromRound<T, P> for Complex
    where Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T, prec: P, round: Round2) -> (Complex, Ordering2) {
        let mut ret = Complex::new(prec);
        let ord = ret.assign_round(t, round);
        (ret, ord)
    }
}

impl Display for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

impl<T> Assign<T> for Complex
where
    Complex: AssignRound<T,
                         Round = Round2,
                         Ordering = Ordering2>,
{
    fn assign(&mut self, other: T) {
        self.assign_round(other, NEAREST);
    }
}

impl AssignRound<Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    fn assign_round(&mut self, other: Complex, round: Round2) -> Ordering2 {
        self.assign_round(&other, round)
    }
}

impl<'a> AssignRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    fn assign_round(&mut self, other: &Complex, round: Round2) -> Ordering2 {
        let mpc_ret =
            unsafe { mpc::set(self.inner_mut(), other.inner(), rraw2(round)) };
        ordering2(mpc_ret)
    }
}

macro_rules! assign_ref {
    { $T:ty } => {
        impl<'a> AssignRound<&'a $T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
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
            fn assign_round(&mut self, other: $T, round: Round2) -> Ordering2 {
                let (real, imag) = self.as_mut_real_imag();
                let ord1 = real.assign_round(other, round.0);
                let ord2 = imag.assign_round(0, round.1);
                (ord1, ord2)
            }
        }
    };
}

assign_ref! { Integer }
assign_ref! { Rational }
assign_ref! { Float }
assign! { Integer }
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
    fn assign_round(&mut self, other: (T, U), round: Round2) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        let ord1 = real.assign_round(other.0, round.0);
        let ord2 = imag.assign_round(other.1, round.1);
        (ord1, ord2)
    }
}

ref_math_op1! { struct ProjRef {}; mpc::proj }
ref_math_op1! { struct SquareRef {}; mpc::sqr }
ref_math_op1! { struct SqrtRef {}; mpc::sqrt }
ref_math_op1! { struct ConjugateRef {}; mpc::conj }

pub struct AbsRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<AbsRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: AbsRef<'a>, round: Round) -> Ordering {
        let mpc_ret = unsafe {
            mpc::abs(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        mpc_ret.cmp(&0)
    }
}

pub struct ArgRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<ArgRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: ArgRef<'a>, round: Round) -> Ordering {
        let mpc_ret = unsafe {
            mpc::arg(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        mpc_ret.cmp(&0)
    }
}

ref_math_op1! { struct MulIRef { negative: bool }; xmpc::mul_i }
ref_math_op1! { struct RecipRef {}; xmpc::recip }

pub struct NormRef<'a> {
    ref_self: &'a Complex,
}

impl<'a> AssignRound<NormRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: NormRef<'a>, round: Round) -> Ordering {
        let mpc_ret = unsafe {
            mpc::norm(self.inner_mut(), src.ref_self.inner(), rraw(round))
        };
        mpc_ret.cmp(&0)
    }
}

ref_math_op1! { struct LnRef {}; mpc::log }
ref_math_op1! { struct Log10Ref {}; mpc::log10 }
ref_math_op1! { struct ExpRef {}; mpc::exp }
ref_math_op1! { struct SinRef {}; mpc::sin }
ref_math_op1! { struct CosRef {}; mpc::cos }
ref_math_op1_2! { struct SinCosRef {}; mpc::sin_cos }
ref_math_op1! { struct TanRef {}; mpc::tan }
ref_math_op1! { struct SinhRef {}; mpc::sinh }
ref_math_op1! { struct CoshRef {}; mpc::cosh }
ref_math_op1! { struct TanhRef {}; mpc::tanh }
ref_math_op1! { struct AsinRef {}; mpc::asin }
ref_math_op1! { struct AcosRef {}; mpc::acos }
ref_math_op1! { struct AtanRef {}; mpc::atan }
ref_math_op1! { struct AsinhRef {}; mpc::asinh }
ref_math_op1! { struct AcoshRef {}; mpc::acosh }
ref_math_op1! { struct AtanhRef {}; mpc::atanh }

impl Neg for Complex {
    type Output = Complex;
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    fn neg_assign(&mut self) {
        unsafe {
            mpc::neg(self.inner_mut(), self.inner(), rraw2(NEAREST));
        }
    }
}

impl<'a> Neg for &'a Complex {
    type Output = NegRef<'a>;
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
    fn assign_round(&mut self, src: NegRef<'a>, round: Round2) -> Ordering2 {
        let mpc_ret = unsafe {
            mpc::neg(self.inner_mut(), src.val.inner(), rraw2(round))
        };
        ordering2(mpc_ret)
    }
}

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Ref:ident
    } => {
        impl<'a> $Imp<&'a $T> for Complex {
            type Output = Complex;
            fn $method(self, op: &'a $T) -> Complex {
                self.$method_round(op, NEAREST).0
            }
        }

        impl<'a> $ImpRound<&'a $T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                mut self,
                rhs: &'a $T,
                round: Round2,
            ) -> (Complex, Ordering2) {
                let mpc_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw2(round),
                    )
                };
                (self, ordering2(mpc_ret))
            }
        }

        impl $Imp<$T> for Complex {
            type Output = Complex;
            fn $method(self, op: $T) -> Complex {
                self.$method_round(op, NEAREST).0
            }
        }

        impl $ImpRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                rhs: $T,
                round: Round2,
            ) -> (Complex, Ordering2) {
                self.$method_round(&rhs, round)
            }
        }

        impl<'a> $Imp<&'a $T> for &'a Complex {
            type Output = $Ref<'a>;
            fn $method(self, rhs: &'a $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs: OwnBorrow::Borrow(rhs),
                }
            }
        }

        impl<'a> $ImpAssign<&'a $T> for Complex {
            fn $method_assign(&mut self, rhs: &'a $T) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw2(NEAREST),
                    );
                }
            }
        }

        impl $ImpAssign<$T> for Complex {
            fn $method_assign(&mut self, rhs: $T) {
                self.$method_assign(&rhs);
            }
        }

        pub struct $Ref<'a> {
            lhs: &'a Complex,
            rhs: OwnBorrow<'a, $T>,
        }

        impl<'a> AssignRound<$Ref<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $Ref, round: Round2) -> Ordering2 {
                let mpc_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
                        rraw2(round),
                    )
                };
                ordering2(mpc_ret)
            }
        }
    };
}

macro_rules! arith_commut_complex {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Ref:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Complex,
            $func,
            $Ref
        }

        impl<'a> $Imp<Complex> for &'a Complex {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }
    }
}

macro_rules! arith_noncommut_complex {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $func:path,
        $Ref:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Complex,
            $func,
            $Ref
        }

        impl<'a> $Imp<Complex> for &'a Complex {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                mut rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                let mpc_ret = unsafe {
                    $func(
                        rhs.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw2(round),
                    )
                };
                (rhs, ordering2(mpc_ret))
            }
        }

        impl<'a> $ImpFromAssign<&'a Complex> for Complex {
            fn $method_from_assign(&mut self, lhs: &Complex) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
                        rraw2(NEAREST),
                    );
                }
            }
        }

        impl $ImpFromAssign for Complex {
            fn $method_from_assign(&mut self, lhs: Complex) {
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
        $Ref:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Ref
        }

        impl<'a> $Imp<$T> for &'a Complex {
            type Output = $Ref<'a>;
            fn $method(self, rhs: $T) -> $Ref<'a> {
                $Ref {
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
        $Ref:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Ref
        }

        impl<'a> $Imp<Complex> for &'a $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self,
                             rhs: Complex,
                             round: Round2,
            ) -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for &'a $T {
            type Output = $Ref<'a>;
            fn $method(self, rhs: &'a Complex) -> $Ref<'a> {
                rhs.$method(self)
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $Ref<'a>;
            fn $method(self, rhs: &'a Complex) -> $Ref<'a> {
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
        $Ref:ident,
        $RefFrom:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Ref
        }

        impl<'a> $Imp<Complex> for &'a $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                mut rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                let mpc_ret = unsafe {
                    $func_from(
                        rhs.inner_mut(),
                        self.inner(),
                        rhs.inner(),
                        rraw2(round),
                    )
                };
                (rhs, ordering2(mpc_ret))
            }
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                (&self).$method_round(rhs, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for &'a $T {
            type Output = $RefFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: OwnBorrow::Borrow(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $RefFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: OwnBorrow::Own(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $ImpFromAssign<&'a $T> for Complex {
            fn $method_from_assign(&mut self, lhs: &'a $T) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.inner(),
                        self.inner(),
                        rraw2(NEAREST),
                    );
                }
            }
        }

        impl $ImpFromAssign<$T> for Complex {
            fn $method_from_assign(&mut self, lhs: $T) {
                self.$method_from_assign(&lhs);
            }
        }

        pub struct $RefFrom<'a> {
            lhs: OwnBorrow<'a, $T>,
            rhs: &'a Complex,
        }

        impl<'a> AssignRound<$RefFrom<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(
                &mut self,
                src: $RefFrom,
                round: Round2,
            ) -> Ordering2 {
                let mpc_ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.inner(),
                        rraw2(round),
                    )
                };
                ordering2(mpc_ret)
            }
        }
    };
}

arith_commut_complex! {
    Add add, AddRound add_round, AddAssign add_assign, mpc::add, AddRef
}
arith_noncommut_complex! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    mpc::sub,
    SubRef
}
arith_commut_complex! {
    Mul mul, MulRound mul_round, MulAssign mul_assign, mpc::mul, MulRef
}
arith_noncommut_complex! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    mpc::div,
    DivRef
}
arith_noncommut_complex! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    PowFromAssign pow_from_assign,
    mpc::pow,
    PowRef
}

arith_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    Float,
    mpc::add_fr,
    AddRefFloat
}
arith_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    Float,
    mpc::sub_fr,
    mpc::fr_sub,
    SubRefFloat,
    SubFromRefFloat
}
arith_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    Float,
    mpc::mul_fr,
    MulRefFloat
}
arith_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    Float,
    mpc::div_fr,
    mpc::fr_div,
    DivRefFloat,
    DivFromRefFloat
}
arith_forward! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    Float,
    mpc::pow_fr,
    PowRefFloat
}
arith_forward! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    Integer,
    mpc::pow_z,
    PowRefInteger
}

macro_rules! arith_prim {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Ref:ident
    } => {
        impl $Imp<$T> for Complex {
            type Output = Complex;
            fn $method(self, rhs: $T) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                mut self,
                rhs: $T,
                round: Round2,
            ) -> (Complex, Ordering2) {
                let mpc_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        rraw2(round),
                    )
                };
                (self, ordering2(mpc_ret))
            }
        }

        impl<'a> $Imp<$T> for &'a Complex {
            type Output = $Ref<'a>;
            fn $method(self, rhs: $T) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpAssign<$T> for Complex {
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        self.inner(),
                        rhs.into(),
                        rraw2(NEAREST),
                    );
                }
            }
        }

        pub struct $Ref<'a> {
            lhs: &'a Complex,
            rhs: $T,
        }

        impl<'a> AssignRound<$Ref<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $Ref, round: Round2) -> Ordering2 {
                let mpc_ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs.into(),
                        rraw2(round),
                    )
                };
                ordering2(mpc_ret)
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
        $Ref:ident
    }=> {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Ref
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $Ref<'a>;
            fn $method(self, rhs: &'a Complex) -> $Ref<'a> {
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
        $Ref:ident,
        $RefFrom:ident
    } => {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Ref
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(
                self,
                mut rhs: Complex,
                round: Round2,
            ) -> (Complex, Ordering2) {
                let mpc_ret = unsafe {
                    $func_from(
                        rhs.inner_mut(),
                        self.into(),
                        rhs.inner(),
                        rraw2(round),
                    )
                };
                (rhs, ordering2(mpc_ret))
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $RefFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $RefFrom<'a> {
                $RefFrom {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpFromAssign<$T> for Complex {
            fn $method_from_assign(&mut self, lhs: $T) {
                unsafe {
                    $func_from(
                        self.inner_mut(),
                        lhs.into(),
                        self.inner(),
                        rraw2(NEAREST),
                    );
                }
            }
        }

        pub struct $RefFrom<'a> {
            lhs: $T,
            rhs: &'a Complex,
        }

        impl<'a> AssignRound<$RefFrom<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round
                (&mut self,
                 src: $RefFrom,
                 round: Round2,
                ) -> Ordering2 {
                let mpc_ret = unsafe {
                    $func_from(
                        self.inner_mut(),
                        src.lhs.into(),
                        src.rhs.inner(),
                        rraw2(round),
                    )
                };
                ordering2(mpc_ret)
            }
        }
    };
}

arith_prim_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    u32,
    mpc::add_ui,
    AddRefU32
}
arith_prim_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    u32,
    mpc::sub_ui,
    xmpc::ui_sub,
    SubRefU32,
    SubFromRefU32
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    u32,
    mpc::mul_ui,
    MulRefU32
}
arith_prim_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    u32,
    mpc::div_ui,
    xmpc::ui_div,
    DivRefU32,
    DivFromRefU32
}
arith_prim_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    i32,
    xmpc::add_si,
    AddRefI32
}
arith_prim_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    i32,
    xmpc::sub_si,
    xmpc::si_sub,
    SubRefI32,
    SubFromRefI32
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    i32,
    mpc::mul_si,
    MulRefI32
}
arith_prim_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    i32,
    xmpc::div_si,
    xmpc::si_div,
    DivRefI32,
    DivFromRefI32
}

arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    u32,
    mpc::mul_2ui,
    ShlRefU32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    u32,
    mpc::div_2ui,
    ShrRefU32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    u32,
    mpc::pow_ui,
    PowRefU32
}
arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    i32,
    mpc::mul_2si,
    ShlRefI32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    i32,
    mpc::div_2si,
    ShrRefI32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    i32,
    mpc::pow_si,
    PowRefI32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    f64,
    mpc::pow_d,
    PowRefF64
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    f32,
    xmpc::pow_single,
    PowRefF32
}

impl<'a> Add<MulRef<'a>> for Complex {
    type Output = Complex;
    /// Peforms multiplication and addition together, with only one
    /// rounding operation to the nearest.
    fn add(self, rhs: MulRef) -> Complex {
        self.add_round(rhs, NEAREST).0
    }
}

impl<'a> AddRound<MulRef<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    type Output = Complex;
    /// Peforms multiplication and addition together with only one
    /// rounding operation as specified.
    fn add_round(mut self, rhs: MulRef, round: Round2) -> (Complex, Ordering2) {
        let mpc_ret = unsafe {
            mpc::fma(
                self.inner_mut(),
                rhs.lhs.inner(),
                rhs.rhs.inner(),
                self.inner(),
                rraw2(round),
            )
        };
        (self, ordering2(mpc_ret))
    }
}

impl<'a> AddAssign<MulRef<'a>> for Complex {
    /// Peforms multiplication and addition together, with only one
    /// rounding operation to the nearest.
    fn add_assign(&mut self, rhs: MulRef) {
        unsafe {
            mpc::fma(
                self.inner_mut(),
                rhs.lhs.inner(),
                rhs.rhs.inner(),
                self.inner(),
                rraw2(NEAREST),
            );
        }
    }
}

impl PartialEq for Complex {
    fn eq(&self, other: &Complex) -> bool {
        self.real().eq(other.real()) && self.imag().eq(other.imag())
    }
}

impl<T, U> PartialEq<(T, U)> for Complex
where
    Float: PartialEq<T>,
    Float: PartialEq<U>,
{
    fn eq(&self, other: &(T, U)) -> bool {
        self.real().eq(&other.0) && self.imag().eq(&other.1)
    }
}

macro_rules! partial_eq {
    { $($T:ty)* } => {
        $(
            impl PartialEq<$T> for Complex {
                fn eq(&self, other: &$T) -> bool {
                    self.real().eq(other) && self.imag().is_zero()
                }
            }
        )*
    };
}

partial_eq! { Integer Rational Float u32 i32 f64 f32 }

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
/// See the [`Complex::valid_str_radix()`]
/// (struct.Complex.html#method.valid_str_radix) method.
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
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}

fn rraw(round: Round) -> mpfr::rnd_t {
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}

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

fn ordering2(ord: c_int) -> (Ordering, Ordering) {
    // ord == first + 4 * second
    let first = mpc::INEX_RE(ord).cmp(&0);
    let second = mpc::INEX_IM(ord).cmp(&0);
    (first, second)
}

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Complex {
    type Output = mpc_t;
    fn inner(&self) -> &mpc_t {
        &self.inner
    }
}

impl InnerMut for Complex {
    unsafe fn inner_mut(&mut self) -> &mut mpc_t {
        &mut self.inner
    }
}

impl Inner for Float {
    type Output = mpfr::mpfr_t;
    fn inner(&self) -> &mpfr::mpfr_t {
        let ptr = self as *const _ as *const mpfr::mpfr_t;
        unsafe { &*ptr }
    }
}

impl InnerMut for Float {
    unsafe fn inner_mut(&mut self) -> &mut mpfr::mpfr_t {
        let ptr = self as *mut _ as *mut mpfr::mpfr_t;
        &mut *ptr
    }
}

impl Inner for Integer {
    type Output = gmp::mpz_t;
    fn inner(&self) -> &gmp::mpz_t {
        let ptr = self as *const _ as *const gmp::mpz_t;
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
    use ::*;
    use super::*;
    use std::f64;

    #[test]
    fn check_ref_op() {
        let prec = (53, 53);
        let ri1 = (12.25, -1.375);
        let ri2 = (-1.375, 13);
        let lhs = Complex::from((ri1, prec));
        let rhs = Complex::from((ri2, prec));
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Complex::from((-&lhs, prec)), -lhs.clone());
        assert_eq!(Complex::from((&lhs + &rhs, prec)), lhs.clone() + &rhs);
        assert_eq!(Complex::from((&lhs - &rhs, prec)), lhs.clone() - &rhs);
        assert_eq!(Complex::from((&lhs * &rhs, prec)), lhs.clone() * &rhs);
        assert_eq!(Complex::from((&lhs / &rhs, prec)), lhs.clone() / &rhs);
        assert_eq!(
            Complex::from(((&lhs).pow(&rhs), prec)),
            lhs.clone().pow(&rhs)
        );

        assert_eq!(Complex::from((&lhs + pu, prec)), lhs.clone() + pu);
        assert_eq!(Complex::from((&lhs - pu, prec)), lhs.clone() - pu);
        assert_eq!(Complex::from((&lhs * pu, prec)), lhs.clone() * pu);
        assert_eq!(Complex::from((&lhs / pu, prec)), lhs.clone() / pu);
        assert_eq!(Complex::from((&lhs << pu, prec)), lhs.clone() << pu);
        assert_eq!(Complex::from((&lhs >> pu, prec)), lhs.clone() >> pu);
        assert_eq!(Complex::from(((&lhs).pow(pu), prec)), lhs.clone().pow(pu));

        assert_eq!(Complex::from((pu + &lhs, prec)), pu + lhs.clone());
        assert_eq!(Complex::from((pu - &lhs, prec)), pu - lhs.clone());
        assert_eq!(Complex::from((pu * &lhs, prec)), pu * lhs.clone());
        assert_eq!(Complex::from((pu / &lhs, prec)), pu / lhs.clone());

        assert_eq!(Complex::from((&lhs + pi, prec)), lhs.clone() + pi);
        assert_eq!(Complex::from((&lhs - pi, prec)), lhs.clone() - pi);
        assert_eq!(Complex::from((&lhs * pi, prec)), lhs.clone() * pi);
        assert_eq!(Complex::from((&lhs / pi, prec)), lhs.clone() / pi);
        assert_eq!(Complex::from((&lhs << pi, prec)), lhs.clone() << pi);
        assert_eq!(Complex::from((&lhs >> pi, prec)), lhs.clone() >> pi);
        assert_eq!(Complex::from(((&lhs).pow(pi), prec)), lhs.clone().pow(pi));

        assert_eq!(Complex::from((pi + &lhs, prec)), pi + lhs.clone());
        assert_eq!(Complex::from((pi - &lhs, prec)), pi - lhs.clone());
        assert_eq!(Complex::from((pi * &lhs, prec)), pi * lhs.clone());
        assert_eq!(Complex::from((pi / &lhs, prec)), pi / lhs.clone());

        assert_eq!(Complex::from(((&lhs).pow(ps), prec)), lhs.clone().pow(ps));
        assert_eq!(Complex::from(((&lhs).pow(pd), prec)), lhs.clone().pow(pd));
    }

    #[test]
    fn check_from_str() {
        let mut c = Complex::new((53, 53));
        c.assign_str("(+0 -0)").unwrap();
        assert_eq!(c, (0, 0));
        assert!(!c.real().get_sign());
        assert!(c.imag().get_sign());
        c.assign_str("(5 6)").unwrap();
        assert_eq!(c, (5, 6));
        c.assign_str_radix("(50 60)", 8).unwrap();
        assert_eq!(c, (0o50, 0o60));
        c.assign_str_radix("33", 16).unwrap();
        assert_eq!(c, (0x33, 0));

        let bad_strings = [
            ("(0,0)", None),
            ("(0 0 )", None),
            ("( 0 0)", None),
            ("( 0)", None),
            ("(0 )", None),
            (" ( 2)", None),
            ("+(1 1)", None),
            ("-(1. 1.)", None),
            ("(1 1@1a(", Some(16)),
            ("(8 9)", Some(9)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Complex::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings =
            [
                ("(inf -@inf@)", 10, f64::INFINITY, f64::NEG_INFINITY),
                ("(+0e99 1.)", 2, 0.0, 1.0),
                ("-9.9e1", 10, -99.0, 0.0),
            ];
        for &(s, radix, r, i) in good_strings.into_iter() {
            assert_eq!(
                Complex::from_str_radix(s, radix, (53, 53)).unwrap(),
                (r, i)
            );
        }
    }


    #[test]
    fn check_formatting() {
        let mut c = Complex::new((53, 53));
        c.assign((Special::Zero, Special::MinusZero));
        assert_eq!(format!("{}", c), "(0.0 0.0)");
        assert_eq!(format!("{:?}", c), "(0.0 -0.0)");
        assert_eq!(format!("{:+}", c), "(+0.0 -0.0)");
        c.assign((2.7, f64::NEG_INFINITY));
        assert_eq!(format!("{:.2}", c), "(2.7e0 -inf)");
        assert_eq!(format!("{:+.8}", c), "(+2.7000000e0 -inf)");
        assert_eq!(format!("{:.4e}", c), "(2.700e0 -inf)");
        assert_eq!(format!("{:.4E}", c), "(2.700E0 -inf)");
        assert_eq!(format!("{:16.2}", c), "    (2.7e0 -inf)");
        c.assign((3.5, 11));
        assert_eq!(format!("{:.4b}", c), "(1.110e1 1.011e3)");
        assert_eq!(format!("{:#.4b}", c), "(0b1.110e1 0b1.011e3)");
        assert_eq!(format!("{:.4o}", c), "(3.400e0 1.300e1)");
        assert_eq!(format!("{:#.4o}", c), "(0o3.400e0 0o1.300e1)");
        assert_eq!(format!("{:.2x}", c), "(3.8@0 b.0@0)");
        assert_eq!(format!("{:#.2x}", c), "(0x3.8@0 0xb.0@0)");
        assert_eq!(format!("{:.2X}", c), "(3.8@0 B.0@0)");
        assert_eq!(format!("{:#.2X}", c), "(0x3.8@0 0xB.0@0)");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
    }
}
