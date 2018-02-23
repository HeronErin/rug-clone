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
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use cast::cast;
use ext::mpfr as xmpfr;
use float::{self, OrdFloat, Round, SmallFloat, Special};
use float::arith::{AddMulIncomplete, MulAddMulIncomplete, MulSubMulIncomplete,
                   SubMulFromIncomplete};
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use inner::{Inner, InnerMut};
use misc;
use ops::{AddAssignRound, AssignRound, NegAssign};
#[cfg(feature = "rand")]
use rand::RandState;
use std::{i32, u32};
#[allow(unused_imports)]
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CString;
use std::marker::PhantomData;
use std::mem;
use std::num::FpCategory;
use std::ops::{Add, AddAssign, Deref};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
use std::ptr;
use std::slice;

#[inline]
pub(crate) fn raw_round(round: Round) -> mpfr::rnd_t {
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
pub(crate) fn ordering1(ord: c_int) -> Ordering {
    ord.cmp(&0)
}

#[inline]
fn ordering2(ord: c_int) -> (Ordering, Ordering) {
    // ord == first + 4 * second
    let first = match ord & 3 {
        2 => -1,
        0 => 0,
        1 => 1,
        _ => unreachable!(),
    };
    let second = match ord >> 2 {
        2 => -1,
        0 => 0,
        1 => 1,
        _ => unreachable!(),
    };
    (ordering1(first), ordering1(second))
}

/// A multi-precision floating-point number with arbitrarily large
/// precision and correct rounding
///
/// The precision has to be set during construction. The rounding
/// method of the required operations can be specified, and the
/// direction of the rounding is returned.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::Round;
/// use rug::ops::DivAssignRound;
/// use std::cmp::Ordering;
/// // A precision of 32 significant bits is specified here.
/// // (The primitive `f32` has a precision of 24 and
/// // `f64` has a precision of 53.)
/// let mut two_thirds_down = Float::with_val(32, 2.0);
/// let dir = two_thirds_down.div_assign_round(3.0, Round::Down);
/// // since we rounded down, direction is Ordering::Less
/// assert_eq!(dir, Ordering::Less);
/// let mut two_thirds_up = Float::with_val(32, 2.0);
/// let dir = two_thirds_up.div_assign_round(3.0, Round::Up);
/// // since we rounded up, direction is Ordering::Greater
/// assert_eq!(dir, Ordering::Greater);
/// let diff_expected = 2.0_f64.powi(-32);
/// let diff = two_thirds_up - two_thirds_down;
/// assert_eq!(diff, diff_expected);
/// ```
///
/// Operations on two borrowed `Float` numbers result in an
/// [incomplete computation value][incomplete] that has to be assigned
/// to a new `Float` value.
///
/// ```rust
/// use rug::Float;
/// let a = Float::with_val(53, 10.5);
/// let b = Float::with_val(53, -1.25);
/// let a_b_ref = &a + &b;
/// let a_b = Float::with_val(53, a_b_ref);
/// assert_eq!(a_b, 9.25);
/// ```
///
/// As a special case, when an
/// [incomplete computation value][incomplete] is obtained from
/// multiplying two `Float` references, it can be added to or
/// subtracted from another `Float` (or reference). This will result
/// in a fused multiply-accumulate operation, with only one rounding
/// operation taking place.
///
/// ```rust
/// use rug::Float;
/// // Use only 4 bits of precision for demonstration purposes.
/// // 24 in binary is 11000.
/// let a = Float::with_val(4, 24);
/// // 1.5 in binary is 1.1.
/// let mul1 = Float::with_val(4, 1.5);
/// // -13 in binary is -1101.
/// let mul2 = Float::with_val(4, -13);
/// // 24 + 1.5 * -13 = 4.5
/// let add = Float::with_val(4, &a + &mul1 * &mul2);
/// assert_eq!(add, 4.5);
/// // 24 - 1.5 * -13 = 43.5, rounded to 44 using four bits of precision.
/// let sub = a - &mul1 * &mul2;
/// assert_eq!(sub, 44);
///
/// // With separate addition and multiplication:
/// let a = Float::with_val(4, 24);
/// // No borrows, so multiplication is computed immediately.
/// // 1.5 * -13 = -19.5 (binary -10011.1), rounded to -20.
/// let separate_add = a + mul1 * mul2;
/// assert_eq!(separate_add, 4);
/// ```
///
/// The [incomplete computation value][incomplete] obtained from
/// multiplying two `Float` references can also be added to or
/// subtracted from another such incomplete value, so that two
/// muliplications and an addition are fused with only one rounding
/// operation taking place.
///
/// ```rust
/// use rug::Float;
/// let a = Float::with_val(53, 24);
/// let b = Float::with_val(53, 1.5);
/// let c = Float::with_val(53, 12);
/// let d = Float::with_val(53, 2);
/// // 24 * 1.5 + 12 * 2 = 60
/// let add = Float::with_val(53, &a * &b + &c * &d);
/// assert_eq!(add, 60);
/// // 24 * 1.5 - 12 * 2 = 12
/// let sub = Float::with_val(53, &a * &b - &c * &d);
/// assert_eq!(sub, 12);
/// ```
///
/// The `Float` type supports various functions. Most methods have
/// four versions:
///
/// 1. The first method consumes the operand and rounds the returned
///    `Float` to the [nearest](float/enum.Round.html#variant.Nearest)
///    representable value.
/// 2. The second method has a `_mut` suffix, mutates the operand and
///    rounds it the nearest representable value.
/// 3. The third method has a `_round` suffix, mutates the operand,
///    applies the specified [rounding method](float/enum.Round.html),
///    and returns the rounding direction:
///    * `Ordering::Less` if the stored value is less than the exact
///      result,
///    * `Ordering::Equal` if the stored value is equal to the exact
///      result,
///    * `Ordering::Greater` if the stored value is greater than the
///      exact result.
/// 4. The fourth method has a `_ref` suffix and borrows the operand.
///    The returned item can be assigned to a `Float`, and the
///    rounding method is selected during the assignment.
///
/// ```rust
/// use rug::Float;
/// use rug::float::Round;
/// use std::cmp::Ordering;
/// let expected = 0.9490_f64;
///
/// // 1. consume the operand, round to nearest
/// let a = Float::with_val(53, 1.25);
/// let sin_a = a.sin();
/// assert!((sin_a - expected).abs() < 0.0001);
///
/// // 2. mutate the operand, round to nearest
/// let mut b = Float::with_val(53, 1.25);
/// b.sin_mut();
/// assert!((b - expected).abs() < 0.0001);
///
/// // 3. mutate the operand, apply specified rounding
/// let mut c = Float::with_val(4, 1.25);
/// // using 4 significant bits, 0.9490 is rounded down to 0.9375
/// let dir = c.sin_round(Round::Nearest);
/// assert_eq!(c, 0.9375);
/// assert_eq!(dir, Ordering::Less);
///
/// // 4. borrow the operand
/// let d = Float::with_val(53, 1.25);
/// let r = d.sin_ref();
/// let sin_d = Float::with_val(53, r);
/// assert!((sin_d - expected).abs() < 0.0001);
/// // d was not consumed
/// assert_eq!(d, 1.25);
/// ```
///
/// The following example is a translation of the [MPFR
/// sample](http://www.mpfr.org/sample.html) found on the MPFR
/// website. The program computes a lower bound on
/// 1 + 1/1! + 1/2! + … + 1/100!
/// using 200-bit precision. The program writes:
///
/// `Sum is 2.7182818284590452353602874713526624977572470936999595749669131`
///
/// ```rust
/// extern crate rug;
/// use rug::Float;
/// use rug::float::{Round};
/// use rug::ops::{AddAssignRound, AssignRound, MulAssignRound};
///
/// fn main() {
///     let mut t = Float::with_val(200, 1.0);
///     let mut s = Float::with_val(200, 1.0);
///     let mut u = Float::new(200);
///     for i in 1..101_u32 {
///         // multiply t by i in place, round towards plus infinity
///         t.mul_assign_round(i, Round::Up);
///         // set u to 1/t, round towards minus infinity
///         u.assign_round(t.recip_ref(), Round::Down);
///         // increase s by u in place, round towards minus infinity
///         s.add_assign_round(&u, Round::Down);
///     }
///     // `None` means the number of printed digits depends on the precision
///     let sr = s.to_string_radix_round(10, None, Round::Down);
///     println!("Sum is {}", sr);
/// #   assert_eq!(
/// #       sr,
/// #       "2.7182818284590452353602874713526624977572470936999595749669131"
/// #   );
/// }
/// ```
///
/// [incomplete]: index.html#incomplete-computation-values
pub struct Float {
    inner: mpfr_t,
}

macro_rules! ref_math_op0_float {
    (
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        ref_math_op0_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $(#[$attr_ref])*
            struct $Incomplete { $($param: $T),* }
        }
    };
}

macro_rules! math_op1_float {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($($param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        math_op1_round! {
            Round => Ordering;
            $func, raw_round => ordering1;
            $(#[$attr])*
            fn $method($($param: $T),*);
            $(#[$attr_mut])*
            fn $method_mut;
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Incomplete;
        }
    };
}

macro_rules! ref_math_op1_float {
    (
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        ref_math_op1_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $(#[$attr_ref])*
            struct $Incomplete { $($param: $T),* }
        }
    };
}

macro_rules! math_op1_2_float {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($rop: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        math_op1_2_round! {
            Round => (Ordering, Ordering);
            $func, raw_round => ordering2;
            $(#[$attr])*
            fn $method($rop $(, $param: $T)*);
            $(#[$attr_mut])*
            fn $method_mut;
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Incomplete;
        }
    };
}

macro_rules! ref_math_op1_2_float {
    (
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $($param: ident: $T: ty),* }
    ) => {
        ref_math_op1_2_round! {
            Float, Round => (Ordering, Ordering);
            $func, raw_round => ordering2;
            $(#[$attr_ref])*
            struct $Incomplete { $($param: $T),* }
        }
    };
}

macro_rules! math_op2_float {
    (
        $func: path;
        $(#[$attr: meta])*
        fn $method: ident($op: ident $(, $param: ident: $T: ty),*);
        $(#[$attr_mut: meta])*
        fn $method_mut: ident;
        $(#[$attr_round: meta])*
        fn $method_round: ident;
        $(#[$attr_ref: meta])*
        fn $method_ref: ident -> $Incomplete: ident;
    ) => {
        math_op2_round! {
            Round => Ordering;
            $func, raw_round => ordering1;
            $(#[$attr])*
            fn $method($op $(, $param: $T)*);
            $(#[$attr_mut])*
            fn $method_mut;
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Incomplete;
        }
    };
}

macro_rules! ref_math_op2_float {
    (
        $func: path;
        $(#[$attr_ref: meta])*
        struct $Incomplete: ident { $op: ident $(, $param: ident: $T: ty),* }
    ) => {
        ref_math_op2_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $(#[$attr_ref])*
            struct $Incomplete { $op $(, $param: $T)* }
        }
    };
}

impl Float {
    /// Create a new floating-point number with the specified
    /// precision and with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::new(53);
    /// assert_eq!(f.prec(), 53);
    /// assert_eq!(f, 0);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn new(prec: u32) -> Self {
        Self::with_val(prec, Special::Zero)
    }

    /// Create a new floating-point number with the specified
    /// precision and with the given value, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::with_val(53, 1.3);
    /// assert_eq!(f.prec(), 53);
    /// assert_eq!(f, 1.3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn with_val<T>(prec: u32, val: T) -> Self
    where
        Float: Assign<T>,
    {
        let mut ret = Float::new_nan(prec);
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
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let (f1, dir) = Float::with_val_round(4, 3.3, Round::Nearest);
    /// // 3.3 with precision 4 is rounded down to 3.25
    /// assert_eq!(f1.prec(), 4);
    /// assert_eq!(f1, 3.25);
    /// assert_eq!(dir, Ordering::Less);
    /// let (f2, dir) = Float::with_val_round(4, 3.3, Round::Up);
    /// // 3.3 rounded up to 3.5
    /// assert_eq!(f2.prec(), 4);
    /// assert_eq!(f2, 3.5);
    /// assert_eq!(dir, Ordering::Greater);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn with_val_round<T>(
        prec: u32,
        val: T,
        round: Round,
    ) -> (Self, Ordering)
    where
        Self: AssignRound<T, Round = Round, Ordering = Ordering>,
    {
        let mut ret = Float::new_nan(prec);
        let ord = ret.assign_round(val, round);
        (ret, ord)
    }

    #[inline]
    fn new_nan(prec: u32) -> Self {
        assert!(
            prec >= float::prec_min() && prec <= float::prec_max(),
            "precision out of range"
        );
        unsafe {
            let mut ret: Float = mem::uninitialized();
            mpfr::init2(ret.inner_mut(), cast(prec));
            ret
        }
    }

    /// Returns the precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::new(53);
    /// assert_eq!(f.prec(), 53);
    /// ```
    #[inline]
    pub fn prec(&self) -> u32 {
        unsafe { cast(mpfr::get_prec(self.inner())) }
    }

    /// Sets the precision, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // 16.25 has seven significant bits (binary 10000.01)
    /// let mut f = Float::with_val(53, 16.25);
    /// f.set_prec(5);
    /// assert_eq!(f, 16);
    /// assert_eq!(f.prec(), 5);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn set_prec(&mut self, prec: u32) {
        self.set_prec_round(prec, Round::Nearest);
    }

    /// Sets the precision, applying the specified rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // 16.25 has seven significant bits (binary 10000.01)
    /// let mut f = Float::with_val(53, 16.25);
    /// let dir = f.set_prec_round(5, Round::Up);
    /// assert_eq!(f, 17);
    /// assert_eq!(dir, Ordering::Greater);
    /// assert_eq!(f.prec(), 5);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn set_prec_round(&mut self, prec: u32, round: Round) -> Ordering {
        assert!(
            prec >= float::prec_min() && prec <= float::prec_max(),
            "precision out of range"
        );
        let ret = unsafe {
            mpfr::prec_round(self.inner_mut(), cast(prec), raw_round(round))
        };
        ordering1(ret)
    }

    /// Parses a `Float` with the specified precision, rounding to the
    /// nearest.
    #[deprecated(since = "0.10.0",
                 note = "use `with_val` and `parse` instead; \
                         `Float::from_str(src, prec)?` can be replaced with \
                         `Float::with_val(prec, Float::parse(src)?)`.")]
    #[inline]
    pub fn from_str(src: &str, prec: u32) -> Result<Self, ParseFloatError> {
        Ok(Float::with_val(prec, Float::parse(src)?))
    }

    /// Parses a `Float` with the specified precision, applying the
    /// specified rounding.
    #[deprecated(
        since = "0.10.0",
        note = "use `with_val_round` and `parse` instead; \
                `Float::from_str_round(src, prec, round)?` can be replaced \
                with \
                `Float::with_val_round(prec, Float::parse(src)?, round)`.")]
    #[inline]
    pub fn from_str_round(
        src: &str,
        prec: u32,
        round: Round,
    ) -> Result<(Self, Ordering), ParseFloatError> {
        Ok(Float::with_val_round(prec, Float::parse(src)?, round))
    }

    /// Parses a `Float` with the specified radix and precision,
    /// rounding to the nearest.
    #[deprecated(
        since = "0.10.0",
        note = "use `with_val` and `parse_radix` instead; \
                `Float::from_str_radix(src, radix, prec)?` can be replaced \
                with \
                `Float::with_val(prec, Float::parse_radix(src, radix)?)`.")]
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
        prec: u32,
    ) -> Result<Self, ParseFloatError> {
        Ok(Float::with_val(prec, Float::parse_radix(src, radix)?))
    }

    /// Parses a `Float` with the specified radix and precision,
    /// applying the specified rounding.
    #[deprecated(
        since = "0.10.0",
        note = "use `with_val_round` and `parse_radix` instead; \
                `Float::from_str_radix_round(src, radix, prec, round)?` can be \
                replaced with \
       `Float::with_val_round(prec, Float::parse_radix(src, radix)?, round)`.")]
    #[inline]
    pub fn from_str_radix_round(
        src: &str,
        radix: i32,
        prec: u32,
        round: Round,
    ) -> Result<(Self, Ordering), ParseFloatError> {
        Ok(Float::with_val_round(
            prec,
            Float::parse_radix(src, radix)?,
            round,
        ))
    }

    /// Parses a decimal string or byte slice into a `Float`.
    ///
    /// `AssignRound<Src> for Float` is implemented with the unwrapped
    /// returned object as `Src`.
    ///
    /// The string can start with an optional minus or plus sign and
    /// must then have one or more significant digits with an optional
    /// decimal point. This can optionally be followed by an exponent;
    /// the exponent can start with a separator 'e', 'E' or '@', and
    /// is followed by an optional minus or plus sign and by one or
    /// more decimal digits.
    ///
    /// Alternatively, the string can indicate the special values
    /// infinity or NaN. Infinity can be represented as "inf,
    /// "infinity", "@inf@" or "@infinity@",and NaN can be represented
    /// as "nan" or "@nan@". All of these special representations are
    /// case insensitive. The NaN representation may also include a
    /// possibly-empty string of ASCII letters, digits and underscores
    /// enclosed in brackets, e.g. `"nan(char_sequence_1)"`.
    ///
    /// ASCII whitespace is ignored everywhere in the string except in
    /// the substrings specified above for special values; for example
    /// " @inf@ " is accepted but "@ inf @" is not. Underscores are
    /// ignored anywhere in digit strings except before the first
    /// digit and between the exponent separator and the first digit
    /// of the exponent.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    ///
    /// let valid = Float::parse("12.25e-4");
    /// let f = Float::with_val(53, valid.unwrap());
    /// assert_eq!(f, 12.25e-4);
    ///
    /// let invalid = Float::parse(".e-4");
    /// assert!(invalid.is_err());
    /// ```
    pub fn parse<S: AsRef<[u8]>>(
        src: S,
    ) -> Result<ParseIncomplete, ParseFloatError> {
        parse(src.as_ref(), 10)
    }

    /// Parses a string or byte slice into a `Float`.
    ///
    /// `AssignRound<Src> for Float` is implemented with the unwrapped
    /// returned object as `Src`.
    ///
    /// The string can start with an optional minus or plus sign and
    /// must then have one or more significant digits with an optional
    /// point. This can optionally be followed by an exponent; the
    /// exponent can start with a separator 'e' or 'E' if the radix ≤
    /// 10, or '@' for any radix, and is followed by an optional minus
    /// or plus sign and by one or more decimal digits.
    ///
    /// Alternatively, the string can indicate the special values
    /// infinity or NaN. If the radix ≤ 10, infinity can be
    /// represented as "inf" or "infinity", and NaN can be represented
    /// as "nan". For any radix, infinity can also be represented as
    /// "@inf@" or "@infinity@", and NaN can be represented as
    /// "@nan@". All of these special representations are case
    /// insensitive. The NaN representation may also include a
    /// possibly-empty string of ASCII letters, digits and underscores
    /// enclosed in brackets, e.g. `"nan(char_sequence_1)"`.
    ///
    /// ASCII whitespace is ignored everywhere in the string except in
    /// the substrings specified above for special values; for example
    /// " @inf@ " is accepted but "@ inf @" is not. Underscores are
    /// ignored anywhere in digit strings except before the first
    /// digit and between the exponent separator and the first digit
    /// of the exponent.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    ///
    /// let valid1 = Float::parse_radix("12.23e-4", 4);
    /// let f1 = Float::with_val(53, valid1.unwrap());
    /// assert_eq!(f1, (2.0 + 4.0 * 1.0 + 0.25 * (2.0 + 0.25 * 3.0)) / 256.0);
    /// let valid2 = Float::parse_radix("12.yz@2", 36);
    /// let f2 = Float::with_val(53, valid2.unwrap());
    /// assert_eq!(f2, 35 + 36 * (34 + 36 * (2 + 36 * 1)));
    ///
    /// let invalid = Float::parse_radix("ffe-2", 16);
    /// assert!(invalid.is_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn parse_radix<S: AsRef<[u8]>>(
        src: S,
        radix: i32,
    ) -> Result<ParseIncomplete, ParseFloatError> {
        parse(src.as_ref(), radix)
    }

    /// Checks if a `Float` can be parsed.
    #[deprecated(since = "0.10.0",
                 note = "use `parse_radix` instead; \
                         `Float::valid_str_radix(src, radix)` can be \
                         replaced with `Float::parse_radix(src, radix)`.")]
    #[inline]
    #[allow(deprecated)]
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidFloat, ParseFloatError> {
        Float::parse_radix(src, radix).map(|inner| ValidFloat {
            inner,
            phantom: PhantomData,
        })
    }

    #[cfg(feature = "integer")]
    /// Converts to an integer, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::with_val(53, 13.7);
    /// let i = match f.to_integer() {
    ///     Some(i) => i,
    ///     None => unreachable!(),
    /// };
    /// assert_eq!(i, 14);
    /// ```
    #[inline]
    pub fn to_integer(&self) -> Option<Integer> {
        self.to_integer_round(Round::Nearest).map(|x| x.0)
    }

    #[cfg(feature = "integer")]
    /// Converts to an integer, applying the specified rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let f = Float::with_val(53, 13.7);
    /// let (i, dir) = match f.to_integer_round(Round::Down) {
    ///     Some(i_dir) => i_dir,
    ///     None => unreachable!(),
    /// };
    /// assert_eq!(i, 13);
    /// assert_eq!(dir, Ordering::Less);
    /// ```
    #[inline]
    pub fn to_integer_round(
        &self,
        round: Round,
    ) -> Option<(Integer, Ordering)> {
        if !self.is_finite() {
            return None;
        }
        let mut i = Integer::new();
        let ret = unsafe {
            mpfr::get_z(i.inner_mut(), self.inner(), raw_round(round))
        };
        Some((i, ordering1(ret)))
    }

    #[cfg(feature = "integer")]
    /// If the value is a [finite number](#method.is_finite), returns
    /// an [`Integer`](struct.Integer.html) and exponent such that
    /// `self` is exactly equal to the integer multiplied by two
    /// raised to the power of the exponent.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::float::Special;
    /// let mut float = Float::with_val(16, 6.5);
    /// // 6.5 in binary is 110.1
    /// // Since the precision is 16 bits, this becomes
    /// // 1101_0000_0000_0000 times two to the power of -12
    /// let (int, exp) = float.to_integer_exp().unwrap();
    /// assert_eq!(int, 0b1101_0000_0000_0000);
    /// assert_eq!(exp, -13);
    ///
    /// float.assign(0);
    /// let (zero, _) = float.to_integer_exp().unwrap();
    /// assert_eq!(zero, 0);
    ///
    /// float.assign(Special::Infinity);
    /// assert!(float.to_integer_exp().is_none());
    /// ```
    #[inline]
    pub fn to_integer_exp(&self) -> Option<(Integer, i32)> {
        if !self.is_finite() {
            return None;
        }
        let mut i = Integer::new();
        let exp = unsafe { mpfr::get_z_2exp(i.inner_mut(), self.inner()) };
        Some((i, cast(exp)))
    }

    #[cfg(feature = "rational")]
    /// If the value is a [finite number](#method.is_finite), returns
    /// a [`Rational`](struct.Rational.html) number preserving all the
    /// precision of the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Float, Rational};
    /// use rug::float::Round;
    /// use std::str::FromStr;
    /// use std::cmp::Ordering;
    ///
    /// // Consider the number 123,456,789 / 10,000,000,000.
    /// let parse = Float::parse("0.0123456789").unwrap();
    /// let (f, f_rounding) = Float::with_val_round(35, parse, Round::Down);
    /// assert_eq!(f_rounding, Ordering::Less);
    /// let r = Rational::from_str("123456789/10000000000").unwrap();
    /// // Set fr to the value of f exactly.
    /// let fr = f.to_rational().unwrap();
    /// // Since f == fr and f was rounded down, r != fr.
    /// assert_ne!(r, fr);
    /// let (frf, frf_rounding) = Float::with_val_round(35, &fr, Round::Down);
    /// assert_eq!(frf_rounding, Ordering::Equal);
    /// assert_eq!(frf, f);
    /// assert_eq!(format!("{:.9}", frf), "1.23456789e-2");
    /// ```
    ///
    /// In the following example, the `Float` values can be
    /// represented exactly.
    ///
    /// ```rust
    /// use rug::Float;
    ///
    /// let large_f = Float::with_val(16, 6.5);
    /// let large_r = large_f.to_rational().unwrap();
    /// let small_f = Float::with_val(16, -0.125);
    /// let small_r = small_f.to_rational().unwrap();
    ///
    /// assert_eq!(*large_r.numer(), 13);
    /// assert_eq!(*large_r.denom(), 2);
    /// assert_eq!(*small_r.numer(), -1);
    /// assert_eq!(*small_r.denom(), 8);
    /// ```
    #[inline]
    pub fn to_rational(&self) -> Option<Rational> {
        if !self.is_finite() {
            return None;
        }
        let mut r = Rational::new();
        unsafe {
            mpfr::get_q(r.inner_mut(), self.inner());
        }
        Some(r)
    }

    /// Converts to an `i32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use std::{i32, u32};
    /// let mut f = Float::with_val(53, -13.7);
    /// assert_eq!(f.to_i32_saturating(), Some(-14));
    /// f.assign(-1e40);
    /// assert_eq!(f.to_i32_saturating(), Some(i32::MIN));
    /// f.assign(u32::MAX);
    /// assert_eq!(f.to_i32_saturating(), Some(i32::MAX));
    /// ```
    #[inline]
    pub fn to_i32_saturating(&self) -> Option<i32> {
        self.to_i32_saturating_round(Round::Nearest)
    }

    /// Converts to an `i32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// let f = Float::with_val(53, -13.7);
    /// assert_eq!(f.to_i32_saturating_round(Round::Up), Some(-13));
    /// ```
    #[inline]
    pub fn to_i32_saturating_round(&self, round: Round) -> Option<i32> {
        if self.is_nan() {
            return None;
        }
        let i = unsafe { mpfr::get_si(self.inner(), raw_round(round)) };
        if i >= c_long::from(i32::MAX) {
            Some(i32::MAX)
        } else if i <= c_long::from(i32::MIN) {
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use std::u32;
    /// let mut f = Float::with_val(53, 13.7);
    /// assert_eq!(f.to_u32_saturating(), Some(14));
    /// f.assign(-1);
    /// assert_eq!(f.to_u32_saturating(), Some(0));
    /// f.assign(1e40);
    /// assert_eq!(f.to_u32_saturating(), Some(u32::MAX));
    /// ```
    #[inline]
    pub fn to_u32_saturating(&self) -> Option<u32> {
        self.to_u32_saturating_round(Round::Nearest)
    }

    /// Converts to a `u32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// let f = Float::with_val(53, 13.7);
    /// assert_eq!(f.to_u32_saturating_round(Round::Down), Some(13));
    /// ```
    #[inline]
    pub fn to_u32_saturating_round(&self, round: Round) -> Option<u32> {
        if self.is_nan() {
            return None;
        }
        let u = unsafe { mpfr::get_ui(self.inner(), raw_round(round)) };
        if u >= c_ulong::from(u32::MAX) {
            Some(u32::MAX)
        } else {
            Some(u as u32)
        }
    }

    /// Converts to an `f32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use std::f32;
    /// let mut f = Float::with_val(53, 13.7);
    /// assert_eq!(f.to_f32(), 13.7);
    /// f.assign(1e300);
    /// assert_eq!(f.to_f32(), f32::INFINITY);
    /// f.assign(1e-300);
    /// assert_eq!(f.to_f32(), 0.0);
    /// ```
    #[inline]
    pub fn to_f32(&self) -> f32 {
        self.to_f32_round(Round::Nearest)
    }

    /// Converts to an `f32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::f32;
    /// let f = Float::with_val(53, 1.0 + (-50f64).exp2());
    /// assert_eq!(f.to_f32_round(Round::Up), 1.0 + f32::EPSILON);
    /// ```
    #[inline]
    pub fn to_f32_round(&self, round: Round) -> f32 {
        unsafe { xmpfr::get_f32(self.inner(), raw_round(round)) }
    }

    /// Converts to an `f64`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use std::f64;
    /// let mut f = Float::with_val(53, 13.7);
    /// assert_eq!(f.to_f64(), 13.7);
    /// f.assign(1e300);
    /// f.square_mut();
    /// assert_eq!(f.to_f64(), f64::INFINITY);
    /// ```
    #[inline]
    pub fn to_f64(&self) -> f64 {
        self.to_f64_round(Round::Nearest)
    }

    /// Converts to an `f64`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::f64;
    /// // (2.0 ^ -90) + 1
    /// let f: Float = Float::with_val(100, -90).exp2() + 1;
    /// assert_eq!(f.to_f64_round(Round::Up), 1.0 + f64::EPSILON);
    /// ```
    #[inline]
    pub fn to_f64_round(&self, round: Round) -> f64 {
        unsafe { mpfr::get_d(self.inner(), raw_round(round)) }
    }

    /// Converts to an `f32` and an exponent, rounding to the nearest.
    ///
    /// The returned `f32` is in the range 0.5 ≤ *x* < 1.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let zero = Float::new(64);
    /// let (d0, exp0) = zero.to_f32_exp();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let three_eighths = Float::with_val(64, 0.375);
    /// let (d3_8, exp3_8) = three_eighths.to_f32_exp();
    /// assert_eq!((d3_8, exp3_8), (0.75, -1));
    /// ```
    #[inline]
    pub fn to_f32_exp(&self) -> (f32, i32) {
        self.to_f32_exp_round(Round::Nearest)
    }

    /// Converts to an `f32` and an exponent, applying the specified
    /// rounding method.
    ///
    /// The returned `f32` is in the range 0.5 ≤ *x* < 1.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// let frac_10_3 = Float::with_val(64, 10) / 3u32;
    /// let (f_down, exp_down) = frac_10_3.to_f32_exp_round(Round::Down);
    /// assert_eq!((f_down, exp_down), (0.8333333, 2));
    /// let (f_up, exp_up) = frac_10_3.to_f32_exp_round(Round::Up);
    /// assert_eq!((f_up, exp_up), (0.8333334, 2));
    /// ```
    #[inline]
    pub fn to_f32_exp_round(&self, round: Round) -> (f32, i32) {
        let mut sf = SmallFloat::from(0.0f32);
        assert_eq!(sf.prec(), 24);
        // since we won't change precision, we can mutate the Float
        let mut exp: c_long = 0;
        let f = unsafe {
            // mpfr::set will not change precision of sf, so we can
            // use the unsafe as_nonreallocating_float function
            mpfr::set(
                sf.as_nonreallocating_float().inner_mut(),
                self.inner(),
                raw_round(round),
            );
            mpfr::get_d_2exp(&mut exp, sf.inner(), raw_round(round))
        };
        (f as f32, cast(exp))
    }

    /// Converts to an `f64` and an exponent, rounding to the nearest.
    ///
    /// The returned `f64` is in the range 0.5 ≤ *x* < 1.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let zero = Float::new(64);
    /// let (d0, exp0) = zero.to_f64_exp();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let three_eighths = Float::with_val(64, 0.375);
    /// let (d3_8, exp3_8) = three_eighths.to_f64_exp();
    /// assert_eq!((d3_8, exp3_8), (0.75, -1));
    /// ```
    #[inline]
    pub fn to_f64_exp(&self) -> (f64, i32) {
        self.to_f64_exp_round(Round::Nearest)
    }

    /// Converts to an `f64` and an exponent, applying the specified
    /// rounding method.
    ///
    /// The returned `f64` is in the range 0.5 ≤ *x* < 1.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// let frac_10_3 = Float::with_val(64, 10) / 3u32;
    /// let (f_down, exp_down) = frac_10_3.to_f64_exp_round(Round::Down);
    /// assert_eq!((f_down, exp_down), (0.8333333333333333, 2));
    /// let (f_up, exp_up) = frac_10_3.to_f64_exp_round(Round::Up);
    /// assert_eq!((f_up, exp_up), (0.8333333333333334, 2));
    /// ```
    #[inline]
    pub fn to_f64_exp_round(&self, round: Round) -> (f64, i32) {
        let mut exp: c_long = 0;
        let f = unsafe {
            mpfr::get_d_2exp(&mut exp, self.inner(), raw_round(round))
        };
        (f, cast(exp))
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
    /// use rug::Float;
    /// use rug::float::Special;
    /// let neg_inf = Float::with_val(53, Special::NegInfinity);
    /// assert_eq!(neg_inf.to_string_radix(10, None), "-inf");
    /// assert_eq!(neg_inf.to_string_radix(16, None), "-@inf@");
    /// let twentythree = Float::with_val(8, 23);
    /// assert_eq!(twentythree.to_string_radix(10, None), "2.300e1");
    /// assert_eq!(twentythree.to_string_radix(16, None), "1.70@1");
    /// assert_eq!(twentythree.to_string_radix(10, Some(2)), "2.3e1");
    /// assert_eq!(twentythree.to_string_radix(16, Some(4)), "1.700@1");
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
        self.to_string_radix_round(radix, num_digits, Round::Nearest)
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` applying the specified rounding method.
    ///
    /// The exponent is encoded in decimal. The output string will have
    /// enough precision such that reading it again will give the exact
    /// same number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// let twentythree = Float::with_val(8, 23.3);
    /// let down = twentythree.to_string_radix_round(10, Some(2), Round::Down);
    /// assert_eq!(down, "2.3e1");
    /// let up = twentythree.to_string_radix_round(10, Some(2), Round::Up);
    /// assert_eq!(up, "2.4e1");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix_round(
        &self,
        radix: i32,
        num_digits: Option<usize>,
        round: Round,
    ) -> String {
        let mut s = String::new();
        append_to_string(&mut s, self, radix, num_digits, round, false);
        s
    }

    /// Parses a `Float` from a string, rounding to the nearest.
    #[inline]
    #[deprecated(since = "0.10.0",
                 note = "use `parse` instead; `f.assign_str(src)?` can be \
                         replaced with `f.assign(Float::parse(src)?)`.")]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseFloatError> {
        self.assign_round(Float::parse(src)?, Round::Nearest);
        Ok(())
    }

    /// Parses a `Float` from a string, applying the specified
    /// rounding.
    #[deprecated(since = "0.10.0",
                 note = "use `parse` instead; \
                         `f.assign_str_round(src, round)?` can be replaced \
                         with `f.assign_round(Float::parse(src)?, round)`.")]
    #[inline]
    pub fn assign_str_round(
        &mut self,
        src: &str,
        round: Round,
    ) -> Result<Ordering, ParseFloatError> {
        Ok(self.assign_round(Float::parse(src)?, round))
    }

    /// Parses a `Float` from a string with the specified radix,
    /// rounding to the nearest.
    #[deprecated(since = "0.10.0",
                 note = "use `parse_radix` instead; \
                         `f.assign_str_radix(src, radix)?` can be replaced \
                         with `f.assign(Float::parse_radix(src, radix)?)`.")]
    #[inline]
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseFloatError> {
        self.assign_round(Float::parse_radix(src, radix)?, Round::Nearest);
        Ok(())
    }

    /// Parses a `Float` from a string with the specified radix,
    /// applying the specified rounding.
    #[deprecated(
        since = "0.10.0",
        note = "use `parse_radix` instead; \
                `f.assign_str_radix_round(src, round)?` can be replaced with \
                `f.assign_round(Float::parse_radix(src, radix)?, round)`.")]
    #[inline]
    pub fn assign_str_radix_round(
        &mut self,
        src: &str,
        radix: i32,
        round: Round,
    ) -> Result<Ordering, ParseFloatError> {
        Ok(self.assign_round(Float::parse_radix(src, radix)?, round))
    }

    /// Creates a `Float` from an initialized MPFR floating-point
    /// number.
    ///
    /// # Safety
    ///
    /// * The value must be initialized.
    /// * The `gmp_mpfr_sys::mpfr::mpfr_t` type can be considered as a
    ///   kind of pointer, so there can be multiple copies of it.
    ///   Since this function takes over ownership, no other copies of
    ///   the passed value should exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::mpfr;
    /// use rug::Float;
    /// use std::mem;
    /// fn main() {
    ///     let f = unsafe {
    ///         let mut m = mem::uninitialized();
    ///         mpfr::init2(&mut m, 53);
    ///         mpfr::set_d(&mut m, -14.5, mpfr::rnd_t::RNDN);
    ///         // m is initialized and unique
    ///         Float::from_raw(m)
    ///     };
    ///     assert_eq!(f, -14.5);
    ///     // since f is a Float now, deallocation is automatic
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw(raw: mpfr_t) -> Self {
        Float { inner: raw }
    }

    /// Converts a `Float` into an MPFR floating-point number.
    ///
    /// The returned object should be freed to avoid memory leaks.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::mpfr;
    /// use rug::Float;
    /// fn main() {
    ///     let f = Float::with_val(53, -14.5);
    ///     let mut m = f.into_raw();
    ///     unsafe {
    ///         let d = mpfr::get_d(&m, mpfr::rnd_t::RNDN);
    ///         assert_eq!(d, -14.5);
    ///         // free object to prevent memory leak
    ///         mpfr::clear(&mut m);
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn into_raw(self) -> mpfr_t {
        let ret = self.inner;
        mem::forget(self);
        ret
    }

    /// Returns a pointer to the internal MPFR floating-point number.
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::mpfr;
    /// use rug::Float;
    /// fn main() {
    ///     let f = Float::with_val(53, -14.5);
    ///     let m_ptr = f.as_raw();
    ///     unsafe {
    ///         let d = mpfr::get_d(m_ptr, mpfr::rnd_t::RNDN);
    ///         assert_eq!(d, -14.5);
    ///     }
    ///     // f is still valid
    ///     assert_eq!(f, -14.5);
    /// }
    /// ```
    #[inline]
    pub fn as_raw(&self) -> *const mpfr_t {
        self.inner()
    }

    /// Returns an unsafe mutable pointer to the internal MPFR
    /// floating-point number.
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::mpfr;
    /// use rug::Float;
    /// fn main() {
    ///     let mut f = Float::with_val(53, -14.5);
    ///     let m_ptr = f.as_raw_mut();
    ///     unsafe {
    ///         mpfr::add_ui(m_ptr, m_ptr, 10, mpfr::rnd_t::RNDN);
    ///     }
    ///     assert_eq!(f, -4.5);
    /// }
    /// ```
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut mpfr_t {
        unsafe { self.inner_mut() }
    }

    /// Borrows a negated copy of the `Float`.
    ///
    /// The returned object implements `Deref<Target = Float>`.
    ///
    /// This method performs a shallow copy and negates it, and
    /// negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::with_val(53, 4.2);
    /// let neg_f = f.as_neg();
    /// assert_eq!(*neg_f, -4.2);
    /// // methods taking &self can be used on the returned object
    /// let reneg_f = neg_f.as_neg();
    /// assert_eq!(*reneg_f, 4.2);
    /// assert_eq!(*reneg_f, f);
    /// ```
    pub fn as_neg(&self) -> BorrowFloat {
        let mut ret = BorrowFloat {
            inner: self.inner,
            phantom: PhantomData,
        };
        ret.inner.sign.neg_assign();
        if self.is_nan() {
            unsafe {
                mpfr::set_nanflag();
            }
        }
        ret
    }

    /// Borrows an absolute copy of the `Float`.
    ///
    /// The returned object implements `Deref<Target = Float>`.
    ///
    /// This method performs a shallow copy and possibly negates it,
    /// and negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let f = Float::with_val(53, -4.2);
    /// let abs_f = f.as_abs();
    /// assert_eq!(*abs_f, 4.2);
    /// // methods taking &self can be used on the returned object
    /// let reabs_f = abs_f.as_abs();
    /// assert_eq!(*reabs_f, 4.2);
    /// assert_eq!(*reabs_f, *abs_f);
    /// ```
    pub fn as_abs(&self) -> BorrowFloat {
        let mut ret = BorrowFloat {
            inner: self.inner,
            phantom: PhantomData,
        };
        ret.inner.sign = 1;
        if self.is_nan() {
            unsafe {
                mpfr::set_nanflag();
            }
        }
        ret
    }

    /// Borrows the `Float` as an ordered float of type
    /// [`OrdFloat`](float/struct.OrdFloat.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Special;
    /// use std::cmp::Ordering;
    ///
    /// let nan_f = Float::with_val(53, Special::Nan);
    /// let nan = nan_f.as_ord();
    /// assert_eq!(nan.cmp(nan), Ordering::Equal);
    ///
    /// let neg_inf_f = Float::with_val(53, Special::NegInfinity);
    /// let neg_inf = neg_inf_f.as_ord();
    /// assert_eq!(nan.cmp(neg_inf), Ordering::Less);
    ///
    /// let zero_f = Float::with_val(53, Special::Zero);
    /// let zero = zero_f.as_ord();
    /// let neg_zero_f = Float::with_val(53, Special::NegZero);
    /// let neg_zero = neg_zero_f.as_ord();
    /// assert_eq!(zero.cmp(neg_zero), Ordering::Greater);
    /// ```
    pub fn as_ord(&self) -> &OrdFloat {
        unsafe { &*(self as *const _ as *const _) }
    }

    /// Returns `true` if `self` is an integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut f = Float::with_val(53, 13.5);
    /// assert!(!f.is_integer());
    /// f *= 2;
    /// assert!(f.is_integer());
    /// ```
    #[inline]
    pub fn is_integer(&self) -> bool {
        unsafe { mpfr::integer_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is not a number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut f = Float::with_val(53, 0);
    /// assert!(!f.is_nan());
    /// f /= 0;
    /// assert!(f.is_nan());
    /// ```
    #[inline]
    pub fn is_nan(&self) -> bool {
        unsafe { mpfr::nan_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus infinity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut f = Float::with_val(53, 1);
    /// assert!(!f.is_infinite());
    /// f /= 0;
    /// assert!(f.is_infinite());
    /// ```
    #[inline]
    pub fn is_infinite(&self) -> bool {
        unsafe { mpfr::inf_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a finite number,
    /// that is neither NaN nor infinity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut f = Float::with_val(53, 1);
    /// assert!(f.is_finite());
    /// f /= 0;
    /// assert!(!f.is_finite());
    /// ```
    #[inline]
    pub fn is_finite(&self) -> bool {
        unsafe { mpfr::number_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::float::Special;
    /// let mut f = Float::with_val(53, Special::Zero);
    /// assert!(f.is_zero());
    /// f.assign(Special::NegZero);
    /// assert!(f.is_zero());
    /// f += 1;
    /// assert!(!f.is_zero());
    /// ```
    #[inline]
    pub fn is_zero(&self) -> bool {
        unsafe { mpfr::zero_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a normal number, that is neither
    /// NaN, nor infinity, nor zero. Note that `Float` cannot be
    /// subnormal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::float::Special;
    /// let mut f = Float::with_val(53, Special::Zero);
    /// assert!(!f.is_normal());
    /// f += 5.2;
    /// assert!(f.is_normal());
    /// f.assign(Special::Infinity);
    /// assert!(!f.is_normal());
    /// f.assign(Special::Nan);
    /// assert!(!f.is_normal());
    /// ```
    #[inline]
    pub fn is_normal(&self) -> bool {
        unsafe { mpfr::regular_p(self.inner()) != 0 }
    }

    /// Returns the floating-point category of the number. Note that
    /// `Float` cannot be subnormal.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Special;
    /// use std::num::FpCategory;
    /// let nan = Float::with_val(53, Special::Nan);
    /// let infinite = Float::with_val(53, Special::Infinity);
    /// let zero = Float::with_val(53, Special::Zero);
    /// let normal = Float::with_val(53, 2.3);
    /// assert_eq!(nan.classify(), FpCategory::Nan);
    /// assert_eq!(infinite.classify(), FpCategory::Infinite);
    /// assert_eq!(zero.classify(), FpCategory::Zero);
    /// assert_eq!(normal.classify(), FpCategory::Normal);
    /// ```
    #[inline]
    pub fn classify(&self) -> FpCategory {
        let inner: *const mpfr_t = self.inner();
        unsafe {
            if mpfr::nan_p(inner) != 0 {
                FpCategory::Nan
            } else if mpfr::inf_p(inner) != 0 {
                FpCategory::Infinite
            } else if mpfr::zero_p(inner) != 0 {
                FpCategory::Zero
            } else {
                FpCategory::Normal
            }
        }
    }

    /// Returns the same result as `self.partial_cmp(&0)`, but is
    /// faster.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::float::Special;
    /// use std::cmp::Ordering;
    /// let mut f = Float::with_val(53, Special::NegZero);
    /// assert_eq!(f.cmp0(), Some(Ordering::Equal));
    /// f += 5.2;
    /// assert_eq!(f.cmp0(), Some(Ordering::Greater));
    /// f.assign(Special::NegInfinity);
    /// assert_eq!(f.cmp0(), Some(Ordering::Less));
    /// f.assign(Special::Nan);
    /// assert_eq!(f.cmp0(), None);
    /// ```
    #[inline]
    pub fn cmp0(&self) -> Option<Ordering> {
        if self.is_nan() {
            None
        } else {
            let ret = unsafe { mpfr::sgn(self.inner()) };
            Some(ordering1(ret))
        }
    }

    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `cmp0`")]
    #[inline]
    pub fn sign(&self) -> Option<Ordering> {
        self.cmp0()
    }

    /// Compares the absolute values of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use std::cmp::Ordering;
    /// let a = Float::with_val(53, -10);
    /// let b = Float::with_val(53, 4);
    /// assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
    /// assert_eq!(a.cmp_abs(&b), Some(Ordering::Greater));
    /// ```
    #[inline]
    pub fn cmp_abs(&self, other: &Self) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(ordering1(mpfr::cmpabs(self.inner(), other.inner()))),
                _ => None,
            }
        }
    }

    /// Returns the exponent of `self` if `self` is a normal number,
    /// otherwise `None`.
    ///
    /// The significand is assumed to be in the range 0.5 ≤ *x* < 1.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// // -(2.0 ^ 32) == -(0.5 * 2 ^ 33)
    /// let mut f = Float::with_val(53, -32f64.exp2());
    /// assert_eq!(f.get_exp(), Some(33));
    /// // 0.8 * 2 ^ -39
    /// f.assign(0.8 * (-39f64).exp2());
    /// assert_eq!(f.get_exp(), Some(-39));
    /// f.assign(0);
    /// assert_eq!(f.get_exp(), None);
    /// ```
    #[inline]
    pub fn get_exp(&self) -> Option<i32> {
        if self.is_normal() {
            let e = unsafe { mpfr::get_exp(self.inner()) };
            Some(cast(e))
        } else {
            None
        }
    }

    /// Returns `true` if the value is positive, +0 or NaN without a
    /// negative sign.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let pos = Float::with_val(53, 1.0);
    /// let neg = Float::with_val(53, -1.0);
    /// assert!(pos.is_sign_positive());
    /// assert!(!neg.is_sign_positive());
    /// ```
    #[inline]
    pub fn is_sign_positive(&self) -> bool {
        !self.is_sign_negative()
    }

    /// Returns `true` if the value is negative, −0 or NaN with a
    /// negative sign.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let neg = Float::with_val(53, -1.0);
    /// let pos = Float::with_val(53, 1.0);
    /// assert!(neg.is_sign_negative());
    /// assert!(!pos.is_sign_negative());
    /// ```
    #[inline]
    pub fn is_sign_negative(&self) -> bool {
        unsafe { mpfr::signbit(self.inner()) != 0 }
    }

    /// Sets to the next value towards `to`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let to = Float::with_val(8, 100);
    /// // 32.5 in binary is 100000.10
    /// // 32.75 in binary is 100000.11
    /// let mut f = Float::with_val(8, 32.5);
    /// f.next_toward(&to);
    /// assert_eq!(f, 32.75);
    /// ```
    #[inline]
    pub fn next_toward(&mut self, to: &Self) {
        unsafe {
            mpfr::nexttoward(self.inner_mut(), to.inner());
        }
    }

    /// Sets to the next value towards +∞.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // 32.5 in binary is 100000.10
    /// // 32.75 in binary is 100000.11
    /// let mut f = Float::with_val(8, 32.5);
    /// f.next_up();
    /// assert_eq!(f, 32.75);
    /// ```
    #[inline]
    pub fn next_up(&mut self) {
        unsafe {
            mpfr::nextabove(self.inner_mut());
        }
    }

    /// Sets to the next value towards −∞.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // 32.5 in binary is 100000.10
    /// // 32.25 in binary is 100000.01
    /// let mut f = Float::with_val(8, 32.5);
    /// f.next_down();
    /// assert_eq!(f, 32.25);
    /// ```
    #[inline]
    pub fn next_down(&mut self) {
        unsafe {
            mpfr::nextbelow(self.inner_mut());
        }
    }

    /// Emulate subnormal numbers for precisions specified in IEEE
    /// 754, rounding to the nearest.
    ///
    /// Subnormalization is only performed for precisions specified in
    /// IEEE 754:
    ///
    /// * binary16 with 16 storage bits and a precision of 11 bits,
    /// * binary32 (single precision) with 32 storage bits and a
    ///   precision of 24 bits,
    /// * binary64 (double precision) with 64 storage bits and a
    ///   precision of 53 bits,
    /// * binary{<i>k</i>} with *k* storage bits where *k* is a
    ///   multiple of 32 and *k* ≥ 128, and a precision of
    ///   *k* − round(4 × log<sub>2</sub> *k*) + 13 bits.
    ///
    /// This method has no effect if the value is not in the subnormal
    /// range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use std::f32;
    /// // minimum single subnormal is 0.5 * 2 ^ -148 = 2 ^ -149
    /// let single_min_subnormal = (-149f64).exp2();
    /// assert_eq!(single_min_subnormal, single_min_subnormal as f32 as f64);
    /// let single_cannot = single_min_subnormal * 1.25;
    /// assert_eq!(single_min_subnormal, single_cannot as f32 as f64);
    /// let mut f = Float::with_val(24, single_cannot);
    /// assert_eq!(f.to_f64(), single_cannot);
    /// f.subnormalize_ieee();
    /// assert_eq!(f.to_f64(), single_min_subnormal);
    /// ```
    #[inline]
    pub fn subnormalize_ieee(&mut self) -> &mut Self {
        self.subnormalize_ieee_round(Ordering::Equal, Round::Nearest);
        self
    }

    /// Emulate subnormal numbers for precisions specified in IEEE
    /// 754, applying the specified rounding method.
    ///
    /// Subnormalization is only performed for precisions specified in
    /// IEEE 754:
    ///
    /// * binary16 with 16 storage bits and a precision of 11 bits,
    /// * binary32 (single precision) with 32 storage bits and a
    ///   precision of 24 bits,
    /// * binary64 (double precision) with 64 storage bits and a
    ///   precision of 53 bits,
    /// * binary{<i>k</i>} with *k* storage bits where *k* is a
    ///   multiple of 32 and *k* ≥ 128, and a precision of
    ///   *k* − round(4 × log<sub>2</sub> *k*) + 13 bits.
    ///
    /// This method simply propagates `prev_rounding` if the value is
    /// not in the subnormal range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// use std::f32;
    /// // minimum single subnormal is 0.5 * 2 ^ -148 = 2 ^ -149
    /// let single_min_subnormal = (-149f64).exp2();
    /// assert_eq!(single_min_subnormal, single_min_subnormal as f32 as f64);
    /// let single_cannot = single_min_subnormal * 1.25;
    /// assert_eq!(single_min_subnormal, single_cannot as f32 as f64);
    /// let mut f = Float::with_val(24, single_cannot);
    /// assert_eq!(f.to_f64(), single_cannot);
    /// let dir = f.subnormalize_ieee_round(Ordering::Equal, Round::Up);
    /// assert_eq!(f.to_f64(), single_min_subnormal * 2.0);
    /// assert_eq!(dir, Ordering::Greater);
    /// ```
    pub fn subnormalize_ieee_round(
        &mut self,
        prev_rounding: Ordering,
        round: Round,
    ) -> Ordering {
        let prec = self.prec();
        let exp_bits = match ieee_storage_bits_for_prec(prec) {
            Some(storage_bits) => storage_bits - prec,
            None => return prev_rounding,
        };
        let normal_exp_min = (-1i32 << (exp_bits - 1)) + 3;
        self.subnormalize_round(normal_exp_min, prev_rounding, round)
    }

    /// Emulate subnormal numbers, rounding to the nearest.
    ///
    /// Subnormalization is only performed when the exponent lies
    /// within the subnormal range, that is when
    /// `normal_exp_min` − *precision* + 1 ≤ *exponent* < `normal_exp_min`.
    /// For example, for IEEE 754 single precision, the precision is
    /// 24 and `normal_exp_min` is −125, so the subnormal range would
    /// be −148 ≤ *exponent* < −125.
    ///
    /// This method has no effect if the value is not in the subnormal
    /// range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use std::f32;
    /// // minimum single subnormal is 0.5 * 2 ^ -148 = 2 ^ -149
    /// let single_min_subnormal = (-149f64).exp2();
    /// assert_eq!(single_min_subnormal, single_min_subnormal as f32 as f64);
    /// let single_cannot = single_min_subnormal * 1.25;
    /// assert_eq!(single_min_subnormal, single_cannot as f32 as f64);
    /// let mut f = Float::with_val(24, single_cannot);
    /// assert_eq!(f.to_f64(), single_cannot);
    /// f.subnormalize(-125);
    /// assert_eq!(f.to_f64(), single_min_subnormal);
    /// ```
    #[inline]
    pub fn subnormalize(&mut self, normal_exp_min: i32) -> &mut Self {
        self.subnormalize_round(
            normal_exp_min,
            Ordering::Equal,
            Round::Nearest,
        );
        self
    }

    /// Emulate subnormal numbers, applying the specified rounding
    /// method.
    ///
    /// Subnormalization is only performed when the exponent lies
    /// within the subnormal range, that is when
    /// `normal_exp_min` − *precision* + 1 ≤ *exponent* < `normal_exp_min`.
    /// For example, for IEEE 754 single precision, the precision is
    /// 24 and `normal_exp_min` is −125, so the subnormal range would
    /// be −148 ≤ *exponent* < −125.
    ///
    /// This method simply propagates `prev_rounding` if the value is
    /// not in the subnormal range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// use std::f32;
    /// // minimum single subnormal is 0.5 * 2 ^ -148 = 2 ^ -149
    /// let single_min_subnormal = (-149f64).exp2();
    /// assert_eq!(single_min_subnormal, single_min_subnormal as f32 as f64);
    /// let single_cannot = single_min_subnormal * 1.25;
    /// assert_eq!(single_min_subnormal, single_cannot as f32 as f64);
    /// let mut f = Float::with_val(24, single_cannot);
    /// assert_eq!(f.to_f64(), single_cannot);
    /// let dir = f.subnormalize_round(-125, Ordering::Equal, Round::Up);
    /// assert_eq!(f.to_f64(), single_min_subnormal * 2.0);
    /// assert_eq!(dir, Ordering::Greater);
    /// ```
    pub fn subnormalize_round(
        &mut self,
        normal_exp_min: i32,
        prev_rounding: Ordering,
        round: Round,
    ) -> Ordering {
        if !self.is_normal() {
            return prev_rounding;
        }
        let exp_min: mpfr::exp_t = cast(normal_exp_min);
        let sub_exp_min = exp_min
            .checked_sub(cast::<_, mpfr::exp_t>(self.prec() - 1))
            .expect("overflow");
        let exp = unsafe { mpfr::get_exp(self.inner()) };
        if exp < sub_exp_min || exp >= exp_min {
            return prev_rounding;
        }
        let prev = match prev_rounding {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        };
        unsafe {
            let save_emin = mpfr::get_emin();
            let save_emax = mpfr::get_emax();
            assert!(save_emax >= exp_min, "`normal_exp_min` too large");
            mpfr::set_emin(sub_exp_min);
            mpfr::set_emax(exp_min);
            let ret =
                mpfr::subnormalize(self.inner_mut(), prev, raw_round(round));
            mpfr::set_emin(save_emin);
            mpfr::set_emax(save_emax);
            ordering1(ret)
        }
    }

    /// Adds a list of `Float` values with correct rounding.
    ///
    /// `AssignRound<Src> for Float`, `Add<Src> for Float`,
    /// `AddAssign<Src> for Float` and `AddAssignRound<Src> for Float`
    /// are implemented with the returned object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::AddAssignRound;
    /// use std::cmp::Ordering;
    ///
    /// // Give each value only 4 bits of precision for example purposes.
    /// let values = [
    ///     Float::with_val(4, 5.0),
    ///     Float::with_val(4, 1024.0),
    ///     Float::with_val(4, -1024.0),
    ///     Float::with_val(4, -4.5),
    /// ];
    ///
    /// // The result should still be exact if it fits.
    /// let r = Float::sum(values.iter());
    /// let sum = Float::with_val(4, r);
    /// assert_eq!(sum, 0.5);
    ///
    /// let mut f = Float::with_val(4, 15.0);
    /// // 15.5 using 4 bits of precision becomes 16.0
    /// let r = Float::sum(values.iter());
    /// let dir = f.add_assign_round(r, Round::Nearest);
    /// assert_eq!(f, 16.0);
    /// assert_eq!(dir, Ordering::Greater);
    /// ```
    #[inline]
    pub fn sum<'a, I>(values: I) -> SumIncomplete<'a, I>
    where
        I: Iterator<Item = &'a Self>,
    {
        SumIncomplete { values }
    }

    /// Multiplies and adds in one fused operation, rounding to the
    /// nearest with only one rounding error.
    ///
    /// `a.mul_add(&b, &c)` produces a result like `&a * &b + &c`, but
    /// `a` is consumed and the result produced uses its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let add = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 + 24 = 4.5
    /// let mul_add = mul1.mul_add(&mul2, &add);
    /// assert_eq!(mul_add, 4.5);
    /// ```
    pub fn mul_add(mut self, mul: &Self, add: &Self) -> Self {
        self.mul_add_round(mul, add, Default::default());
        self
    }

    /// Multiplies and adds in one fused operation, rounding to the
    /// nearest with only one rounding error.
    ///
    /// `a.mul_add_mut(&b, &c)` produces a result like `&a * &b + &c`,
    /// but stores the result in `a` using its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mut mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let add = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 + 24 = 4.5
    /// mul1.mul_add_mut(&mul2, &add);
    /// assert_eq!(mul1, 4.5);
    /// ```
    pub fn mul_add_mut(&mut self, mul: &Self, add: &Self) {
        self.mul_add_round(mul, add, Default::default());
    }

    /// Multiplies and adds in one fused operation, applying the
    /// specified rounding method with only one rounding error.
    ///
    /// `a.mul_add_round(&b, &c, round)` produces a result like
    /// `ans.assign_round(&a * &b + &c, round)`, but stores the result
    /// in `a` using its precision rather than in another `Float` like
    /// `ans`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mut mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let add = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 + 24 = 4.5
    /// let dir = mul1.mul_add_round(&mul2, &add, Round::Nearest);
    /// assert_eq!(mul1, 4.5);
    /// assert_eq!(dir, Ordering::Equal);
    /// ```
    pub fn mul_add_round(
        &mut self,
        mul: &Self,
        add: &Self,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fma(
                self.inner_mut(),
                self.inner(),
                mul.inner(),
                add.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }

    /// Multiplies and adds in one fused operation.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// `a.mul_add_ref(&b, &c)` produces the exact same result as
    /// `&a * &b + &c`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let add = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 + 24 = 4.5
    /// let ans = Float::with_val(4, mul1.mul_add_ref(&mul2, &add));
    /// assert_eq!(ans, 4.5);
    /// ```
    pub fn mul_add_ref<'a>(
        &'a self,
        mul: &'a Self,
        add: &'a Self,
    ) -> AddMulIncomplete<'a> {
        self * mul + add
    }

    /// Multiplies and subtracts in one fused operation, rounding to
    /// the nearest with only one rounding error.
    ///
    /// `a.mul_sub(&b, &c)` produces a result like `&a * &b - &c`, but
    /// `a` is consumed and the result produced uses its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let sub = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 - 24 = -43.5, rounded to 44 using four bits of precision.
    /// let mul_sub = mul1.mul_sub(&mul2, &sub);
    /// assert_eq!(mul_sub, -44);
    /// ```
    pub fn mul_sub(mut self, mul: &Self, sub: &Self) -> Self {
        self.mul_sub_round(mul, sub, Default::default());
        self
    }

    /// Multiplies and subtracts in one fused operation, rounding to
    /// the nearest with only one rounding error.
    ///
    /// `a.mul_sub_mut(&b, &c)` produces a result like `&a * &b - &c`,
    /// but stores the result in `a` using its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mut mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let sub = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 - 24 = -43.5, rounded to 44 using four bits of precision.
    /// mul1.mul_sub_mut(&mul2, &sub);
    /// assert_eq!(mul1, -44);
    /// ```
    pub fn mul_sub_mut(&mut self, mul: &Self, sub: &Self) {
        self.mul_sub_round(mul, sub, Default::default());
    }

    /// Multiplies and subtracts in one fused operation, applying the
    /// specified rounding method with only one rounding error.
    ///
    /// `a.mul_sub_round(&b, &c, round)` produces a result like
    /// `ans.assign_round(&a * &b - &c, round)`, but stores the result
    /// in `a` using its precision rather than in another `Float` like
    /// `ans`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mut mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let sub = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 - 24 = -43.5, rounded to 44 using four bits of precision.
    /// let dir = mul1.mul_sub_round(&mul2, &sub, Round::Nearest);
    /// assert_eq!(mul1, -44);
    /// assert_eq!(dir, Ordering::Less);
    /// ```
    pub fn mul_sub_round(
        &mut self,
        mul: &Self,
        sub: &Self,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fms(
                self.inner_mut(),
                self.inner(),
                mul.inner(),
                sub.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }

    /// Multiplies and subtracts in one fused operation.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// `a.mul_sub_ref(&b, &c)` produces the exact same result as
    /// `&a * &b - &c`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// // Use only 4 bits of precision for demonstration purposes.
    /// // 1.5 in binary is 1.1.
    /// let mul1 = Float::with_val(4, 1.5);
    /// // -13 in binary is -1101.
    /// let mul2 = Float::with_val(4, -13);
    /// // 24 in binary is 11000.
    /// let sub = Float::with_val(4, 24);
    ///
    /// // 1.5 * -13 - 24 = -43.5, rounded to 44 using four bits of precision.
    /// let ans = Float::with_val(4, mul1.mul_sub_ref(&mul2, &sub));
    /// assert_eq!(ans, -44);
    /// ```
    pub fn mul_sub_ref<'a>(
        &'a self,
        mul: &'a Self,
        sub: &'a Self,
    ) -> SubMulFromIncomplete<'a> {
        self * mul - sub
    }

    /// Multiplies two products and adds them in one fused operation,
    /// rounding to the nearest with only one rounding error.
    ///
    /// `a.mul_add_mul(&b, &c, &d)` produces a result like
    /// `&a * &b + &c * &d`, but `a` is consumed and the result
    /// produced uses its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 + 12 * 2 = 60
    /// let mul_add_mul = a.mul_add_mul(&b, &c, &d);
    /// assert_eq!(mul_add_mul, 60);
    /// ```
    pub fn mul_add_mul(
        mut self,
        mul: &Self,
        add_mul1: &Self,
        add_mul2: &Self,
    ) -> Self {
        self.mul_add_mul_round(mul, add_mul1, add_mul2, Default::default());
        self
    }

    /// Multiplies two products and adds them in one fused operation,
    /// rounding to the nearest with only one rounding error.
    ///
    /// `a.mul_add_mul_mut(&b, &c, &d)` produces a result like
    /// `&a * &b + &c * &d`, but stores the result in `a` using its
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 + 12 * 2 = 60
    /// a.mul_add_mul_mut(&b, &c, &d);
    /// assert_eq!(a, 60);
    /// ```
    pub fn mul_add_mul_mut(
        &mut self,
        mul: &Self,
        add_mul1: &Self,
        add_mul2: &Self,
    ) {
        self.mul_add_mul_round(mul, add_mul1, add_mul2, Default::default());
    }

    /// Multiplies two produces and adds them in one fused operation,
    /// applying the specified rounding method with only one rounding
    /// error.
    ///
    /// `a.mul_add_mul_round(&b, &c, &d, round)` produces a result
    /// like `ans.assign_round(&a * &b + &c * &d, round)`, but stores
    /// the result in `a` using its precision rather than in another
    /// `Float` like `ans`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 + 12 * 2 = 60
    /// let dir = a.mul_add_mul_round(&b, &c, &d, Round::Nearest);
    /// assert_eq!(a, 60);
    /// assert_eq!(dir, Ordering::Equal);
    /// ```
    pub fn mul_add_mul_round(
        &mut self,
        mul: &Self,
        add_mul1: &Self,
        add_mul2: &Self,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fmma(
                self.inner_mut(),
                self.inner(),
                mul.inner(),
                add_mul1.inner(),
                add_mul2.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }

    /// Multiplies two products and adds them in one fused operation.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// `a.mul_add_mul_ref(&b, &c, &d)` produces the exact same result
    /// as `&a * &b + &c * &d`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 + 12 * 2 = 60
    /// let ans = Float::with_val(53, a.mul_add_mul_ref(&b, &c, &d));
    /// assert_eq!(ans, 60);
    /// ```
    pub fn mul_add_mul_ref<'a>(
        &'a self,
        mul: &'a Self,
        add_mul1: &'a Self,
        add_mul2: &'a Self,
    ) -> MulAddMulIncomplete<'a> {
        self * mul + add_mul1 * add_mul2
    }

    /// Multiplies two products and subtracts them in one fused
    /// operation, rounding to the nearest with only one rounding
    /// error.
    ///
    /// `a.mul_sub_mul(&b, &c, &d)` produces a result like
    /// `&a * &b - &c * &d`, but `a` is consumed and the result
    /// produced uses its precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 - 12 * 2 = 12
    /// let mul_sub_mul = a.mul_sub_mul(&b, &c, &d);
    /// assert_eq!(mul_sub_mul, 12);
    /// ```
    pub fn mul_sub_mul(
        mut self,
        mul: &Self,
        sub_mul1: &Self,
        sub_mul2: &Self,
    ) -> Self {
        self.mul_sub_mul_round(mul, sub_mul1, sub_mul2, Default::default());
        self
    }

    /// Multiplies two products and subtracts them in one fused
    /// operation, rounding to the nearest with only one rounding
    /// error.
    ///
    /// `a.mul_sub_mul_mut(&b, &c, &d)` produces a result like
    /// `&a * &b - &c * &d`, but stores the result in `a` using its
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 - 12 * 2 = 12
    /// a.mul_sub_mul_mut(&b, &c, &d);
    /// assert_eq!(a, 12);
    /// ```
    pub fn mul_sub_mul_mut(
        &mut self,
        mul: &Self,
        sub_mul1: &Self,
        sub_mul2: &Self,
    ) {
        self.mul_sub_mul_round(mul, sub_mul1, sub_mul2, Default::default());
    }

    /// Multiplies two produces and subtracts them in one fused
    /// operation, applying the specified rounding method with only
    /// one rounding error.
    ///
    /// `a.mul_sub_mul_round(&b, &c, &d, round)` produces a result
    /// like `ans.assign_round(&a * &b - &c * &d, round)`, but stores
    /// the result in `a` using its precision rather than in another
    /// `Float` like `ans`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 - 12 * 2 = 12
    /// let dir = a.mul_sub_mul_round(&b, &c, &d, Round::Nearest);
    /// assert_eq!(a, 12);
    /// assert_eq!(dir, Ordering::Equal);
    /// ```
    pub fn mul_sub_mul_round(
        &mut self,
        mul: &Self,
        sub_mul1: &Self,
        sub_mul2: &Self,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fmms(
                self.inner_mut(),
                self.inner(),
                mul.inner(),
                sub_mul1.inner(),
                sub_mul2.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }

    /// Multiplies two products and subtracts them in one fused
    /// operation.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// `a.mul_sub_mul_ref(&b, &c, &d)` produces the exact same result
    /// as `&a * &b - &c * &d`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let a = Float::with_val(53, 24);
    /// let b = Float::with_val(53, 1.5);
    /// let c = Float::with_val(53, 12);
    /// let d = Float::with_val(53, 2);
    /// // 24 * 1.5 - 12 * 2 = 12
    /// let ans = Float::with_val(53, a.mul_sub_mul_ref(&b, &c, &d));
    /// assert_eq!(ans, 12);
    /// ```
    pub fn mul_sub_mul_ref<'a>(
        &'a self,
        mul: &'a Self,
        sub_mul1: &'a Self,
        sub_mul2: &'a Self,
    ) -> MulSubMulIncomplete<'a> {
        self * mul - sub_mul1 * sub_mul2
    }

    math_op1_float! {
        mpfr::sqr;
        /// Computes the square, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 5.0);
        /// let square = f.square();
        /// assert_eq!(square, 25.0);
        /// ```
        fn square();
        /// Computes the square, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 5.0);
        /// f.square_mut();
        /// assert_eq!(f, 25.0);
        /// ```
        fn square_mut;
        /// Computes the square, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(3, 5.0);
        /// // 25 in binary is 11001 (more than 3 bits of precision).
        /// // 25 (11001) is rounded up to 28 (11100).
        /// let dir = f.square_round(Round::Up);
        /// assert_eq!(f, 28.0);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn square_round;
        /// Computes the square.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 5.0);
        /// let r = f.square_ref();
        /// let square = Float::with_val(53, r);
        /// assert_eq!(square, 25.0);
        /// ```
        fn square_ref -> SquareIncomplete;
    }
    math_op1_float! {
        mpfr::sqrt;
        /// Computes the square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 25.0);
        /// let sqrt = f.sqrt();
        /// assert_eq!(sqrt, 5.0);
        /// ```
        fn sqrt();
        /// Computes the square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 25.0);
        /// f.sqrt_mut();
        /// assert_eq!(f, 5.0);
        /// ```
        fn sqrt_mut;
        /// Computes the square root, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(4, 5.0);
        /// // sqrt(5) in binary is 10.00111100...
        /// // sqrt(5) is rounded to 2.25 (10.01).
        /// let dir = f.sqrt_round(Round::Nearest);
        /// assert_eq!(f, 2.25);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn sqrt_round;
        /// Computes the square root.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 25.0);
        /// let r = f.sqrt_ref();
        /// let sqrt = Float::with_val(53, r);
        /// assert_eq!(sqrt, 5.0);
        /// ```
        fn sqrt_ref -> SqrtIncomplete;
    }
    math_op0! {
        /// Computes the square root of `u`.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let s = Float::sqrt_u(25);
        /// let f = Float::with_val(53, s);
        /// assert_eq!(f, 5.0);
        /// ```
        fn sqrt_u(u: u32) -> SqrtUIncomplete;
    }

    /// Sets `self` to the square root of `u`, rounding to the
    /// nearest.
    #[deprecated(since = "0.9.2",
                 note = "use `sqrt_u` instead; `f.assign_sqrt_u(u)` can be \
                         replaced with `f.assign(Float::sqrt_u(u))`.")]
    #[inline]
    pub fn assign_sqrt_u(&mut self, u: u32) {
        self.assign_round(Float::sqrt_u(u), Round::Nearest);
    }

    /// Sets `self` to the square root of `u`, applying the specified
    /// rounding method.
    #[deprecated(since = "0.9.2",
                 note = "use `sqrt_u` instead; \
                         `f.assign_sqrt_u_round(u, round)` can be replaced \
                         with `f.assign_round(Float::sqrt_u(u), round)`.")]
    #[inline]
    pub fn assign_sqrt_u_round(&mut self, u: u32, round: Round) -> Ordering {
        self.assign_round(Float::sqrt_u(u), round)
    }

    math_op1_float! {
        mpfr::rec_sqrt;
        /// Computes the reciprocal square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 16.0);
        /// let recip_sqrt = f.recip_sqrt();
        /// assert_eq!(recip_sqrt, 0.25);
        /// ```
        fn recip_sqrt();
        /// Computes the reciprocal square root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 16.0);
        /// f.recip_sqrt_mut();
        /// assert_eq!(f, 0.25);
        /// ```
        fn recip_sqrt_mut;
        /// Computes the reciprocal square root, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(4, 5.0);
        /// // 1/sqrt(5) in binary is 0.01110010...
        /// // 1/sqrt(5) is rounded to 0.4375 (0.01110).
        /// let dir = f.recip_sqrt_round(Round::Nearest);
        /// assert_eq!(f, 0.4375);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn recip_sqrt_round;
        /// Computes the reciprocal square root.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 16.0);
        /// let r = f.recip_sqrt_ref();
        /// let recip_sqrt = Float::with_val(53, r);
        /// assert_eq!(recip_sqrt, 0.25);
        /// ```
        fn recip_sqrt_ref -> RecipSqrtIncomplete;
    }
    math_op1_float! {
        mpfr::cbrt;
        /// Computes the cube root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 125.0);
        /// let cbrt = f.cbrt();
        /// assert_eq!(cbrt, 5.0);
        /// ```
        fn cbrt();
        /// Computes the cube root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 125.0);
        /// f.cbrt_mut();
        /// assert_eq!(f, 5.0);
        /// ```
        fn cbrt_mut;
        /// Computes the cube root, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(4, 5.0);
        /// // cbrt(5) in binary is 1.101101...
        /// // cbrt(5) is rounded to 1.75 (1.110).
        /// let dir = f.cbrt_round(Round::Nearest);
        /// assert_eq!(f, 1.75);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn cbrt_round;
        /// Computes the cube root.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 125.0);
        /// let r = f.cbrt_ref();
        /// let cbrt = Float::with_val(53, r);
        /// assert_eq!(cbrt, 5.0);
        /// ```
        fn cbrt_ref -> CbrtIncomplete;
    }
    math_op1_float! {
        mpfr::rootn_ui;
        /// Computes the <i>k</i>th root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 625.0);
        /// let root = f.root(4);
        /// assert_eq!(root, 5.0);
        /// ```
        fn root(k: u32);
        /// Computes the <i>k</i>th root, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 625.0);
        /// f.root_mut(4);
        /// assert_eq!(f, 5.0);
        /// ```
        fn root_mut;
        /// Computes the <i>k</i>th root, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(4, 5.0);
        /// // fourth root of 5 in binary is 1.01111...
        /// // fourth root of 5 is rounded to 1.5 (1.100).
        /// let dir = f.root_round(4, Round::Nearest);
        /// assert_eq!(f, 1.5);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn root_round;
        /// Computes the <i>k</i>th root.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 625.0);
        /// let r = f.root_ref(4);
        /// let root = Float::with_val(53, r);
        /// assert_eq!(root, 5.0);
        /// ```
        fn root_ref -> RootIncomplete;
    }
    math_op1_no_round! {
        mpfr::abs, raw_round;
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -23.5);
        /// let abs = f.abs();
        /// assert_eq!(abs, 23.5);
        /// ```
        fn abs();
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -23.5);
        /// f.abs_mut();
        /// assert_eq!(f, 23.5);
        /// ```
        fn abs_mut;
        /// Computes the absolute value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -23.5);
        /// let r = f.abs_ref();
        /// let abs = Float::with_val(53, r);
        /// assert_eq!(abs, 23.5);
        /// ```
        fn abs_ref -> AbsIncomplete;
    }
    math_op1_no_round! {
        xmpfr::signum, raw_round;
        /// Computes the signum.
        ///
        /// * 1.0 if the value is positive, +0.0 or +∞
        /// * −1.0 if the value is negative, −0.0 or −∞
        /// * NaN if the value is NaN
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// assert_eq!(Float::with_val(53, -23.5).signum(), -1);
        /// assert_eq!(Float::with_val(53, -0.0).signum(), -1);
        /// assert_eq!(Float::with_val(53, 0.0).signum(), 1);
        /// assert_eq!(Float::with_val(53, 23.5).signum(), 1);
        /// ```
        fn signum();
        /// Computes the signum.
        ///
        /// * 1.0 if the value is positive, +0.0 or +∞
        /// * −1.0 if the value is negative, −0.0 or −∞
        /// * NaN if the value is NaN
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -23.5);
        /// f.signum_mut();
        /// assert_eq!(f, -1);
        /// ```
        fn signum_mut;
        /// Computes the signum.
        ///
        /// * 1.0 if the value is positive, +0.0 or +∞
        /// * −1.0 if the value is negative, −0.0 or −∞
        /// * NaN if the value is NaN
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -23.5);
        /// let r = f.signum_ref();
        /// let signum = Float::with_val(53, r);
        /// assert_eq!(signum, -1);
        /// ```
        fn signum_ref -> SignumIncomplete;
    }

    /// Clamps the value within the specified bounds, rounding to the
    /// nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let min = -1.5;
    /// let max = 1.5;
    /// let too_small = Float::with_val(53, -2.5);
    /// let clamped1 = too_small.clamp(&min, &max);
    /// assert_eq!(clamped1, -1.5);
    /// let in_range = Float::with_val(53, 0.5);
    /// let clamped2 = in_range.clamp(&min, &max);
    /// assert_eq!(clamped2, 0.5);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value,
    /// unless assigning any of them to `self` produces the same value
    /// with the same rounding direction.
    #[inline]
    pub fn clamp<'a, 'b, Min, Max>(mut self, min: &'a Min, max: &'b Max) -> Self
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
            + AssignRound<&'b Max, Round = Round, Ordering = Ordering>,
    {
        self.clamp_round(min, max, Round::Nearest);
        self
    }

    /// Clamps the value within the specified bounds, rounding to the
    /// nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let min = -1.5;
    /// let max = 1.5;
    /// let mut too_small = Float::with_val(53, -2.5);
    /// too_small.clamp_mut(&min, &max);
    /// assert_eq!(too_small, -1.5);
    /// let mut in_range = Float::with_val(53, 0.5);
    /// in_range.clamp_mut(&min, &max);
    /// assert_eq!(in_range, 0.5);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value,
    /// unless assigning any of them to `self` produces the same value
    /// with the same rounding direction.
    #[inline]
    pub fn clamp_mut<'a, 'b, Min, Max>(&mut self, min: &'a Min, max: &'b Max)
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
            + AssignRound<&'b Max, Round = Round, Ordering = Ordering>,
    {
        self.clamp_round(min, max, Round::Nearest);
    }

    /// Clamps the value within the specified bounds, applying the
    /// specified rounding method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let min = Float::with_val(53, -1.5);
    /// let max = Float::with_val(53, 1.5);
    /// let mut too_small = Float::with_val(53, -2.5);
    /// let dir1 = too_small.clamp_round(&min, &max, Round::Nearest);
    /// assert_eq!(too_small, -1.5);
    /// assert_eq!(dir1, Ordering::Equal);
    /// let mut in_range = Float::with_val(53, 0.5);
    /// let dir2 = in_range.clamp_round(&min, &max, Round::Nearest);
    /// assert_eq!(in_range, 0.5);
    /// assert_eq!(dir2, Ordering::Equal);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value,
    /// unless assigning any of them to `self` produces the same value
    /// with the same rounding direction.
    pub fn clamp_round<'a, 'b, Min, Max>(
        &mut self,
        min: &'a Min,
        max: &'b Max,
        round: Round,
    ) -> Ordering
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
            + AssignRound<&'b Max, Round = Round, Ordering = Ordering>,
    {
        if (*self).lt(min) {
            let dir = self.assign_round(min, round);
            if (*self).gt(max) {
                let dir2 = self.assign_round(max, round);
                assert!(
                    dir == dir2 && !(*self).lt(min),
                    "minimum larger than maximum"
                );
                dir
            } else {
                dir
            }
        } else if (*self).gt(max) {
            let dir = self.assign_round(max, round);
            if (*self).lt(min) {
                let dir2 = self.assign_round(min, round);
                assert!(
                    dir == dir2 && !(*self).gt(max),
                    "minimum larger than maximum"
                );
                dir
            } else {
                dir
            }
        } else {
            if self.is_nan() {
                unsafe {
                    mpfr::set_nanflag();
                }
            }
            Ordering::Equal
        }
    }

    /// Clamps the value within the specified bounds.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let min = -1.5;
    /// let max = 1.5;
    /// let too_small = Float::with_val(53, -2.5);
    /// let r1 = too_small.clamp_ref(&min, &max);
    /// let clamped1 = Float::with_val(53, r1);
    /// assert_eq!(clamped1, -1.5);
    /// let in_range = Float::with_val(53, 0.5);
    /// let r2 = in_range.clamp_ref(&min, &max);
    /// let clamped2 = Float::with_val(53, r2);
    /// assert_eq!(clamped2, 0.5);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value,
    /// unless assigning any of them to the target produces the same
    /// value with the same rounding direction.
    #[inline]
    pub fn clamp_ref<'a, Min, Max>(
        &'a self,
        min: &'a Min,
        max: &'a Max,
    ) -> ClampIncomplete<'a, Min, Max>
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
            + AssignRound<&'a Max, Round = Round, Ordering = Ordering>,
    {
        ClampIncomplete {
            ref_self: self,
            min,
            max,
        }
    }

    math_op1_float! {
        xmpfr::recip;
        /// Computes the reciprocal, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.25);
        /// let recip = f.recip();
        /// assert_eq!(recip, -4.0);
        /// ```
        fn recip();
        /// Computes the reciprocal, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -0.25);
        /// f.recip_mut();
        /// assert_eq!(f, -4.0);
        /// ```
        fn recip_mut;
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 5 in binary is 101
        /// let mut f = Float::with_val(4, -5.0);
        /// // 1/5 in binary is 0.00110011...
        /// // 1/5 is rounded to 0.203125 (0.001101).
        /// let dir = f.recip_round(Round::Nearest);
        /// assert_eq!(f, -0.203125);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn recip_round;
        /// Computes the reciprocal.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.25);
        /// let r = f.recip_ref();
        /// let recip = Float::with_val(53, r);
        /// assert_eq!(recip, -4.0);
        /// ```
        fn recip_ref -> RecipIncomplete;
    }
    math_op2_float! {
        mpfr::min;
        /// Finds the minimum, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, -2);
        /// let min = a.min(&b);
        /// assert_eq!(min, -2);
        /// ```
        fn min(other);
        /// Finds the minimum, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, -2);
        /// a.min_mut(&b);
        /// assert_eq!(a, -2);
        /// ```
        fn min_mut;
        /// Finds the minimum, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, -2);
        /// let dir = a.min_round(&b, Round::Nearest);
        /// assert_eq!(a, -2);
        /// assert_eq!(dir, Ordering::Equal);
        /// ```
        fn min_round;
        /// Finds the minimum.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, -2);
        /// let r = a.min_ref(&b);
        /// let min = Float::with_val(53, r);
        /// assert_eq!(min, -2);
        /// ```
        fn min_ref -> MinIncomplete;
    }
    math_op2_float! {
        mpfr::max;
        /// Finds the maximum, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, 12.5);
        /// let max = a.max(&b);
        /// assert_eq!(max, 12.5);
        /// ```
        fn max(other);
        /// Finds the maximum, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, 12.5);
        /// a.max_mut(&b);
        /// assert_eq!(a, 12.5);
        /// ```
        fn max_mut;
        /// Finds the maximum, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, 12.5);
        /// let dir = a.max_round(&b, Round::Nearest);
        /// assert_eq!(a, 12.5);
        /// assert_eq!(dir, Ordering::Equal);
        /// ```
        fn max_round;
        /// Finds the maximum.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 5.2);
        /// let b = Float::with_val(53, 12.5);
        /// let r = a.max_ref(&b);
        /// let max = Float::with_val(53, r);
        /// assert_eq!(max, 12.5);
        /// ```
        fn max_ref -> MaxIncomplete;
    }
    math_op2_float! {
        mpfr::dim;
        /// Computes the positive difference between `self` and
        /// `other`, rounding to the nearest.
        ///
        /// The positive difference is `self` − `other` if `self` >
        /// `other`, zero if `self` ≤ `other`, or NaN if any operand
        /// is NaN.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 12.5);
        /// let b = Float::with_val(53, 7.3);
        /// let diff1 = a.positive_diff(&b);
        /// assert_eq!(diff1, 5.2);
        /// let diff2 = diff1.positive_diff(&b);
        /// assert_eq!(diff2, 0);
        /// ```
        fn positive_diff(other);
        /// Computes the positive difference between `self` and
        /// `other`, rounding to the nearest.
        ///
        /// The positive difference is `self` − `other` if `self` >
        /// `other`, zero if `self` ≤ `other`, or NaN if any operand
        /// is NaN.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut a = Float::with_val(53, 12.5);
        /// let b = Float::with_val(53, 7.3);
        /// a.positive_diff_mut(&b);
        /// assert_eq!(a, 5.2);
        /// a.positive_diff_mut(&b);
        /// assert_eq!(a, 0);
        /// ```
        fn positive_diff_mut;
        /// Computes the positive difference between `self` and
        /// `other`, applying the specified rounding method.
        ///
        /// The positive difference is `self` − `other` if `self` >
        /// `other`, zero if `self` ≤ `other`, or NaN if any operand
        /// is NaN.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let mut a = Float::with_val(53, 12.5);
        /// let b = Float::with_val(53, 7.3);
        /// let dir = a.positive_diff_round(&b, Round::Nearest);
        /// assert_eq!(a, 5.2);
        /// assert_eq!(dir, Ordering::Equal);
        /// let dir = a.positive_diff_round(&b, Round::Nearest);
        /// assert_eq!(a, 0);
        /// assert_eq!(dir, Ordering::Equal);
        /// ```
        fn positive_diff_round;
        /// Computes the positive difference.
        ///
        /// The positive difference is `self` − `other` if `self` >
        /// `other`, zero if `self` ≤ `other`, or NaN if any operand
        /// is NaN.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let a = Float::with_val(53, 12.5);
        /// let b = Float::with_val(53, 7.3);
        /// let rab = a.positive_diff_ref(&b);
        /// let ab = Float::with_val(53, rab);
        /// assert_eq!(ab, 5.2);
        /// let rba = b.positive_diff_ref(&a);
        /// let ba = Float::with_val(53, rba);
        /// assert_eq!(ba, 0);
        /// ```
        fn positive_diff_ref -> PositiveDiffIncomplete;
    }

    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `positive_diff`")]
    #[inline]
    pub fn pos_diff(self, other: &Self) -> Self {
        self.positive_diff(other)
    }
    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `positive_diff_mut`")]
    #[inline]
    pub fn pos_diff_mut(&mut self, other: &Self) {
        self.positive_diff_mut(other);
    }
    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `positive_diff_round`")]
    #[inline]
    pub fn pos_diff_round(&mut self, other: &Self, round: Round) -> Ordering {
        self.positive_diff_round(other, round)
    }
    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `positive_diff_ref`")]
    #[inline]
    pub fn pos_diff_ref<'a>(
        &'a self,
        other: &'a Self,
    ) -> PositiveDiffIncomplete<'a> {
        self.positive_diff_ref(other)
    }
    #[doc(hidden)]
    #[deprecated(since = "0.6.0", note = "renamed to `positive_diff`")]
    #[inline]
    pub fn abs_diff(self, other: &Self) -> Self {
        self.positive_diff(other)
    }
    #[doc(hidden)]
    #[deprecated(since = "0.6.0", note = "renamed to `positive_diff_mut`")]
    #[inline]
    pub fn abs_diff_mut(&mut self, other: &Self) {
        self.positive_diff_mut(other);
    }
    #[doc(hidden)]
    #[deprecated(since = "0.6.0", note = "renamed to `positive_diff_round`")]
    #[inline]
    pub fn abs_diff_round(&mut self, other: &Self, round: Round) -> Ordering {
        self.positive_diff_round(other, round)
    }
    #[doc(hidden)]
    #[deprecated(since = "0.6.0", note = "renamed to `positive_diff_ref`")]
    #[inline]
    pub fn abs_diff_ref<'a>(
        &'a self,
        other: &'a Self,
    ) -> PositiveDiffIncomplete<'a> {
        self.positive_diff_ref(other)
    }

    math_op1_float! {
        mpfr::log;
        /// Computes the natural logarithm, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let ln = f.ln();
        /// let expected = 0.4055_f64;
        /// assert!((ln - expected).abs() < 0.0001);
        /// ```
        fn ln();
        /// Computes the natural logarithm, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.ln_mut();
        /// let expected = 0.4055_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn ln_mut;
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // ln(1.5) = 0.4055
        /// // using 4 significant bits: 0.40625
        /// let dir = f.ln_round(Round::Nearest);
        /// assert_eq!(f, 0.40625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn ln_round;
        /// Computes the natural logarithm.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let ln = Float::with_val(53, f.ln_ref());
        /// let expected = 0.4055_f64;
        /// assert!((ln - expected).abs() < 0.0001);
        /// ```
        fn ln_ref -> LnIncomplete;
    }
    math_op0! {
        /// Computes the natural logarithm of `u`.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let l = Float::ln_u(3);
        /// let f = Float::with_val(53, l);
        /// let expected = 1.0986f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn ln_u(u: u32) -> LnUIncomplete;
    }

    math_op1_float! {
        mpfr::log2;
        /// Computes the logarithm to base 2, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let log2 = f.log2();
        /// let expected = 0.5850_f64;
        /// assert!((log2 - expected).abs() < 0.0001);
        /// ```
        fn log2();
        /// Computes the logarithm to base 2, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.log2_mut();
        /// let expected = 0.5850_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn log2_mut;
        /// Computes the logarithm to base 2, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // log2(1.5) = 0.5850
        /// // using 4 significant bits: 0.5625
        /// let dir = f.log2_round(Round::Nearest);
        /// assert_eq!(f, 0.5625);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn log2_round;
        /// Computes the logarithm to base 2.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let log2 = Float::with_val(53, f.log2_ref());
        /// let expected = 0.5850_f64;
        /// assert!((log2 - expected).abs() < 0.0001);
        /// ```
        fn log2_ref -> Log2Incomplete;
    }
    math_op1_float! {
        mpfr::log10;
        /// Computes the logarithm to base 10, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let log10 = f.log10();
        /// let expected = 0.1761_f64;
        /// assert!((log10 - expected).abs() < 0.0001);
        /// ```
        fn log10();
        /// Computes the logarithm to base 10, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.log10_mut();
        /// let expected = 0.1761_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn log10_mut;
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // log10(1.5) = 0.1761
        /// // using 4 significant bits: 0.171875
        /// let dir = f.log10_round(Round::Nearest);
        /// assert_eq!(f, 0.171875);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn log10_round;
        /// Computes the logarithm to base 10.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let log10 = Float::with_val(53, f.log10_ref());
        /// let expected = 0.1761_f64;
        /// assert!((log10 - expected).abs() < 0.0001);
        /// ```
        fn log10_ref -> Log10Incomplete;
    }
    math_op1_float! {
        mpfr::exp;
        /// Computes the exponential, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp = f.exp();
        /// let expected = 4.4817_f64;
        /// assert!((exp - expected).abs() < 0.0001);
        /// ```
        fn exp();
        /// Computes the exponential, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.exp_mut();
        /// let expected = 4.4817_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn exp_mut;
        /// Computes the exponential, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // exp(1.5) = 4.4817
        /// // using 4 significant bits: 4.5
        /// let dir = f.exp_round(Round::Nearest);
        /// assert_eq!(f, 4.5);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn exp_round;
        /// Computes the exponential.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp = Float::with_val(53, f.exp_ref());
        /// let expected = 4.4817_f64;
        /// assert!((exp - expected).abs() < 0.0001);
        /// ```
        fn exp_ref -> ExpIncomplete;
    }
    math_op1_float! {
        mpfr::exp2;
        /// Computes 2 to the power of `self`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp2 = f.exp2();
        /// let expected = 2.8284_f64;
        /// assert!((exp2 - expected).abs() < 0.0001);
        /// ```
        fn exp2();
        /// Computes 2 to the power of `self`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.exp2_mut();
        /// let expected = 2.8284_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn exp2_mut;
        /// Computes 2 to the power of `self`, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // exp2(1.5) = 2.8284
        /// // using 4 significant bits: 2.75
        /// let dir = f.exp2_round(Round::Nearest);
        /// assert_eq!(f, 2.75);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn exp2_round;
        /// Computes 2 to the power of the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp2 = Float::with_val(53, f.exp2_ref());
        /// let expected = 2.8284_f64;
        /// assert!((exp2 - expected).abs() < 0.0001);
        /// ```
        fn exp2_ref -> Exp2Incomplete;
    }
    math_op1_float! {
        mpfr::exp10;
        /// Computes 10 to the power of `self`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp10 = f.exp10();
        /// let expected = 31.6228_f64;
        /// assert!((exp10 - expected).abs() < 0.0001);
        /// ```
        fn exp10();
        /// Computes 10 to the power of `self`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.5);
        /// f.exp10_mut();
        /// let expected = 31.6228_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn exp10_mut;
        /// Computes 10 to the power of `self`, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5);
        /// // exp10(1.5) = 31.6228
        /// // using 4 significant bits: 32
        /// let dir = f.exp10_round(Round::Nearest);
        /// assert_eq!(f, 32);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn exp10_round;
        /// Computes 10 to the power of the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.5);
        /// let exp10 = Float::with_val(53, f.exp10_ref());
        /// let expected = 31.6228_f64;
        /// assert!((exp10 - expected).abs() < 0.0001);
        /// ```
        fn exp10_ref -> Exp10Incomplete;
    }
    math_op1_float! {
        mpfr::sin;
        /// Computes the sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sin = f.sin();
        /// let expected = 0.9490_f64;
        /// assert!((sin - expected).abs() < 0.0001);
        /// ```
        fn sin();
        /// Computes the sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.sin_mut();
        /// let expected = 0.9490_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn sin_mut;
        /// Computes the sine, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // sin(1.25) = 0.9490
        /// // using 4 significant bits: 0.9375
        /// let dir = f.sin_round(Round::Nearest);
        /// assert_eq!(f, 0.9375);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn sin_round;
        /// Computes the sine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sin = Float::with_val(53, f.sin_ref());
        /// let expected = 0.9490_f64;
        /// assert!((sin - expected).abs() < 0.0001);
        /// ```
        fn sin_ref -> SinIncomplete;
    }
    math_op1_float! {
        mpfr::cos;
        /// Computes the cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cos = f.cos();
        /// let expected = 0.3153_f64;
        /// assert!((cos - expected).abs() < 0.0001);
        /// ```
        fn cos();
        /// Computes the cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.cos_mut();
        /// let expected = 0.3153_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn cos_mut;
        /// Computes the cosine, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // cos(1.25) = 0.3153
        /// // using 4 significant bits: 0.3125
        /// let dir = f.cos_round(Round::Nearest);
        /// assert_eq!(f, 0.3125);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn cos_round;
        /// Computes the cosine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cos = Float::with_val(53, f.cos_ref());
        /// let expected = 0.3153_f64;
        /// assert!((cos - expected).abs() < 0.0001);
        /// ```
        fn cos_ref -> CosIncomplete;
    }
    math_op1_float! {
        mpfr::tan;
        /// Computes the tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let tan = f.tan();
        /// let expected = 3.0096_f64;
        /// assert!((tan - expected).abs() < 0.0001);
        /// ```
        fn tan();
        /// Computes the tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.tan_mut();
        /// let expected = 3.0096_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn tan_mut;
        /// Computes the tangent, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // tan(1.25) = 3.0096
        /// // using 4 significant bits: 3.0
        /// let dir = f.tan_round(Round::Nearest);
        /// assert_eq!(f, 3.0);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn tan_round;
        /// Computes the tangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let tan = Float::with_val(53, f.tan_ref());
        /// let expected = 3.0096_f64;
        /// assert!((tan - expected).abs() < 0.0001);
        /// ```
        fn tan_ref -> TanIncomplete;
    }
    math_op1_2_float! {
        mpfr::sin_cos;
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let (sin, cos) = f.sin_cos(Float::new(53));
        /// let expected_sin = 0.9490_f64;
        /// let expected_cos = 0.3153_f64;
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
        /// use rug::Float;
        /// let mut sin = Float::with_val(53, 1.25);
        /// let mut cos = Float::new(53);
        /// sin.sin_cos_mut(&mut cos);
        /// let expected_sin = 0.9490_f64;
        /// let expected_cos = 0.3153_f64;
        /// assert!((sin - expected_sin).abs() < 0.0001);
        /// assert!((cos - expected_cos).abs() < 0.0001);
        /// ```
        fn sin_cos_mut;
        /// Computes the sine and cosine of `self`, applying the specified
        /// rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut sin = Float::with_val(4, 1.25);
        /// let mut cos = Float::new(4);
        /// // sin(1.25) = 0.9490, using 4 significant bits: 0.9375
        /// // cos(1.25) = 0.3153, using 4 significant bits: 0.3125
        /// let (dir_sin, dir_cos) =
        ///     sin.sin_cos_round(&mut cos, Round::Nearest);
        /// assert_eq!(sin, 0.9375);
        /// assert_eq!(dir_sin, Ordering::Less);
        /// assert_eq!(cos, 0.3125);
        /// assert_eq!(dir_cos, Ordering::Less);
        /// ```
        fn sin_cos_round;
        /// Computes the sine and cosine.
        ///
        /// `AssignRound<Src> for (Float, Float)` and
        /// `AssignRound<Src> for (&mut Float, &mut Float)` are
        /// implemented with the returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Float};
        /// use rug::float::Round;
        /// use rug::ops::AssignRound;
        /// use std::cmp::Ordering;
        /// let phase = Float::with_val(53, 1.25);
        ///
        /// let (mut sin, mut cos) = (Float::new(53), Float::new(53));
        /// let sin_cos = phase.sin_cos_ref();
        /// (&mut sin, &mut cos).assign(sin_cos);
        /// let expected_sin = 0.9490_f64;
        /// let expected_cos = 0.3153_f64;
        /// assert!((sin - expected_sin).abs() < 0.0001);
        /// assert!((cos - expected_cos).abs() < 0.0001);
        ///
        /// // using 4 significant bits: sin = 0.9375
        /// // using 4 significant bits: cos = 0.3125
        /// let (mut sin_4, mut cos_4) = (Float::new(4), Float::new(4));
        /// let sin_cos = phase.sin_cos_ref();
        /// let (dir_sin, dir_cos) = (&mut sin_4, &mut cos_4)
        ///     .assign_round(sin_cos, Round::Nearest);
        /// assert_eq!(sin_4, 0.9375);
        /// assert_eq!(dir_sin, Ordering::Less);
        /// assert_eq!(cos_4, 0.3125);
        /// assert_eq!(dir_cos, Ordering::Less);
        /// ```
        fn sin_cos_ref -> SinCosIncomplete;
    }
    math_op1_float! {
        mpfr::sec;
        /// Computes the secant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sec = f.sec();
        /// let expected = 3.1714_f64;
        /// assert!((sec - expected).abs() < 0.0001);
        /// ```
        fn sec();
        /// Computes the secant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.sec_mut();
        /// let expected = 3.1714_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn sec_mut;
        /// Computes the secant, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // sec(1.25) = 3.1714
        /// // using 4 significant bits: 3.25
        /// let dir = f.sec_round(Round::Nearest);
        /// assert_eq!(f, 3.25);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn sec_round;
        /// Computes the secant.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sec = Float::with_val(53, f.sec_ref());
        /// let expected = 3.1714_f64;
        /// assert!((sec - expected).abs() < 0.0001);
        /// ```
        fn sec_ref -> SecIncomplete;
    }
    math_op1_float! {
        mpfr::csc;
        /// Computes the cosecant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let csc = f.csc();
        /// let expected = 1.0538_f64;
        /// assert!((csc - expected).abs() < 0.0001);
        /// ```
        fn csc();
        /// Computes the cosecant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.csc_mut();
        /// let expected = 1.0538_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn csc_mut;
        /// Computes the cosecant, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // csc(1.25) = 1.0538
        /// // using 4 significant bits: 1.0
        /// let dir = f.csc_round(Round::Nearest);
        /// assert_eq!(f, 1.0);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn csc_round;
        /// Computes the cosecant.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let csc = Float::with_val(53, f.csc_ref());
        /// let expected = 1.0538_f64;
        /// assert!((csc - expected).abs() < 0.0001);
        /// ```
        fn csc_ref -> CscIncomplete;
    }
    math_op1_float! {
        mpfr::cot;
        /// Computes the cotangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cot = f.cot();
        /// let expected = 0.3323_f64;
        /// assert!((cot - expected).abs() < 0.0001);
        /// ```
        fn cot();
        /// Computes the cotangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.cot_mut();
        /// let expected = 0.3323_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn cot_mut;
        /// Computes the cotangent, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // cot(1.25) = 0.3323
        /// // using 4 significant bits: 0.34375
        /// let dir = f.cot_round(Round::Nearest);
        /// assert_eq!(f, 0.34375);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn cot_round;
        /// Computes the cotangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cot = Float::with_val(53, f.cot_ref());
        /// let expected = 0.3323_f64;
        /// assert!((cot - expected).abs() < 0.0001);
        /// ```
        fn cot_ref -> CotIncomplete;
    }
    math_op1_float! {
        mpfr::asin;
        /// Computes the arc-sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let asin = f.asin();
        /// let expected = -0.8481_f64;
        /// assert!((asin - expected).abs() < 0.0001);
        /// ```
        fn asin();
        /// Computes the arc-sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -0.75);
        /// f.asin_mut();
        /// let expected = -0.8481_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn asin_mut;
        /// Computes the arc-sine, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, -0.75);
        /// // asin(-0.75) = -0.8481
        /// // using 4 significant bits: -0.875
        /// let dir = f.asin_round(Round::Nearest);
        /// assert_eq!(f, -0.875);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn asin_round;
        /// Computes the arc-sine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let asin = Float::with_val(53, f.asin_ref());
        /// let expected = -0.8481_f64;
        /// assert!((asin - expected).abs() < 0.0001);
        /// ```
        fn asin_ref -> AsinIncomplete;
    }
    math_op1_float! {
        mpfr::acos;
        /// Computes the arc-cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let acos = f.acos();
        /// let expected = 2.4189_f64;
        /// assert!((acos - expected).abs() < 0.0001);
        /// ```
        fn acos();
        /// Computes the arc-cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -0.75);
        /// f.acos_mut();
        /// let expected = 2.4189_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn acos_mut;
        /// Computes the arc-cosine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, -0.75);
        /// // acos(-0.75) = 2.4189
        /// // using 4 significant bits: 2.5
        /// let dir = f.acos_round(Round::Nearest);
        /// assert_eq!(f, 2.5);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn acos_round;
        /// Computes the arc-cosine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let acos = Float::with_val(53, f.acos_ref());
        /// let expected = 2.4189_f64;
        /// assert!((acos - expected).abs() < 0.0001);
        /// ```
        fn acos_ref -> AcosIncomplete;
    }
    math_op1_float! {
        mpfr::atan;
        /// Computes the arc-tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let atan = f.atan();
        /// let expected = -0.6435_f64;
        /// assert!((atan - expected).abs() < 0.0001);
        /// ```
        fn atan();
        /// Computes the arc-tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, -0.75);
        /// f.atan_mut();
        /// let expected = -0.6435_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn atan_mut;
        /// Computes the arc-tangent, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, -0.75);
        /// // atan(-0.75) = -0.6435
        /// // using 4 significant bits: -0.625
        /// let dir = f.atan_round(Round::Nearest);
        /// assert_eq!(f, -0.625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn atan_round;
        /// Computes the arc-tangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, -0.75);
        /// let atan = Float::with_val(53, f.atan_ref());
        /// let expected = -0.6435_f64;
        /// assert!((atan - expected).abs() < 0.0001);
        /// ```
        fn atan_ref -> AtanIncomplete;
    }
    math_op2_float! {
        mpfr::atan2;
        /// Computes the arc-tangent2 of `self` and `x`, rounding to
        /// the nearest.
        ///
        /// This is similar to the arc-tangent of `self / x`, but
        /// has an output range of 2<i>π</i> rather than *π*.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let y = Float::with_val(53, 3.0);
        /// let x = Float::with_val(53, -4.0);
        /// let atan2 = y.atan2(&x);
        /// let expected = 2.4981_f64;
        /// assert!((atan2 - expected).abs() < 0.0001);
        /// ```
        fn atan2(x);
        /// Computes the arc-tangent2 of `self` and `x`, rounding to
        /// the nearest.
        ///
        /// This is similar to the arc-tangent of `self / x`, but
        /// has an output range of 2<i>π</i> rather than *π*.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut y = Float::with_val(53, 3.0);
        /// let x = Float::with_val(53, -4.0);
        /// y.atan2_mut(&x);
        /// let expected = 2.4981_f64;
        /// assert!((y - expected).abs() < 0.0001);
        /// ```
        fn atan2_mut;
        /// Computes the arc-tangent2 of `self` and `x`, applying the
        /// specified rounding method.
        ///
        /// This is similar to the arc-tangent of `self / x`, but
        /// has an output range of 2<i>π</i> rather than *π*.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut y = Float::with_val(4, 3.0);
        /// let x = Float::with_val(4, -4.0);
        /// // atan2(3.0, -4.0) = 2.4981
        /// // using 4 significant bits: 2.5
        /// let dir = y.atan2_round(&x, Round::Nearest);
        /// assert_eq!(y, 2.5);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn atan2_round;
        /// Computes the arc-tangent.
        ///
        /// This is similar to the arc-tangent of `self / x`, but
        /// has an output range of 2<i>π</i> rather than *π*.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let y = Float::with_val(53, 3.0);
        /// let x = Float::with_val(53, -4.0);
        /// let r = y.atan2_ref(&x);
        /// let atan2 = Float::with_val(53, r);
        /// let expected = 2.4981_f64;
        /// assert!((atan2 - expected).abs() < 0.0001);
        /// ```
        fn atan2_ref -> Atan2Incomplete;
    }
    math_op1_float! {
        mpfr::sinh;
        /// Computes the hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sinh = f.sinh();
        /// let expected = 1.6019_f64;
        /// assert!((sinh - expected).abs() < 0.0001);
        /// ```
        fn sinh();
        /// Computes the hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.sinh_mut();
        /// let expected = 1.6019_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn sinh_mut;
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // sinh(1.25) = 1.6019
        /// // using 4 significant bits: 1.625
        /// let dir = f.sinh_round(Round::Nearest);
        /// assert_eq!(f, 1.625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn sinh_round;
        /// Computes the hyperbolic sine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sinh = Float::with_val(53, f.sinh_ref());
        /// let expected = 1.6019_f64;
        /// assert!((sinh - expected).abs() < 0.0001);
        /// ```
        fn sinh_ref -> SinhIncomplete;
    }
    math_op1_float! {
        mpfr::cosh;
        /// Computes the hyperbolic cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cosh = f.cosh();
        /// let expected = 1.8884_f64;
        /// assert!((cosh - expected).abs() < 0.0001);
        /// ```
        fn cosh();
        /// Computes the hyperbolic cosine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.cosh_mut();
        /// let expected = 1.8884_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn cosh_mut;
        /// Computes the hyperbolic cosine, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // cosh(1.25) = 1.8884
        /// // using 4 significant bits: 1.875
        /// let dir = f.cosh_round(Round::Nearest);
        /// assert_eq!(f, 1.875);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn cosh_round;
        /// Computes the hyperbolic cosine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let cosh = Float::with_val(53, f.cosh_ref());
        /// let expected = 1.8884_f64;
        /// assert!((cosh - expected).abs() < 0.0001);
        /// ```
        fn cosh_ref -> CoshIncomplete;
    }
    math_op1_float! {
        mpfr::tanh;
        /// Computes the hyperbolic tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let tanh = f.tanh();
        /// let expected = 0.8483_f64;
        /// assert!((tanh - expected).abs() < 0.0001);
        /// ```
        fn tanh();
        /// Computes the hyperbolic tangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.tanh_mut();
        /// let expected = 0.8483_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn tanh_mut;
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // tanh(1.25) = 0.8483
        /// // using 4 significant bits: 0.875
        /// let dir = f.tanh_round(Round::Nearest);
        /// assert_eq!(f, 0.875);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn tanh_round;
        /// Computes the hyperbolic tangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let tanh = Float::with_val(53, f.tanh_ref());
        /// let expected = 0.8483_f64;
        /// assert!((tanh - expected).abs() < 0.0001);
        /// ```
        fn tanh_ref -> TanhIncomplete;
    }
    math_op1_2_float! {
        mpfr::sinh_cosh;
        /// Computes the hyperbolic sine and cosine of `self`,
        /// rounding to the nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let (sinh, cosh) = f.sinh_cosh(Float::new(53));
        /// let expected_sinh = 1.6019_f64;
        /// let expected_cosh = 1.8884_f64;
        /// assert!((sinh - expected_sinh).abs() < 0.0001);
        /// assert!((cosh - expected_cosh).abs() < 0.0001);
        /// ```
        fn sinh_cosh(cos);
        /// Computes the hyperbolic sine and cosine of `self`,
        /// rounding to the nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut sinh = Float::with_val(53, 1.25);
        /// let mut cosh = Float::new(53);
        /// sinh.sinh_cosh_mut(&mut cosh);
        /// let expected_sinh = 1.6019_f64;
        /// let expected_cosh = 1.8884_f64;
        /// assert!((sinh - expected_sinh).abs() < 0.0001);
        /// assert!((cosh - expected_cosh).abs() < 0.0001);
        /// ```
        fn sinh_cosh_mut;
        /// Computes the hyperbolic sine and cosine of `self`,
        /// applying the specified rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut sinh = Float::with_val(4, 1.25);
        /// let mut cosh = Float::new(4);
        /// // sinh(1.25) = 1.6019, using 4 significant bits: 1.625
        /// // cosh(1.25) = 1.8884, using 4 significant bits: 1.875
        /// let (dir_sinh, dir_cosh) =
        ///     sinh.sinh_cosh_round(&mut cosh, Round::Nearest);
        /// assert_eq!(sinh, 1.625);
        /// assert_eq!(dir_sinh, Ordering::Greater);
        /// assert_eq!(cosh, 1.875);
        /// assert_eq!(dir_cosh, Ordering::Less);
        /// ```
        fn sinh_cosh_round;
        /// Computes the hyperbolic sine and cosine.
        ///
        /// `AssignRound<Src> for (Float, Float)` and
        /// `AssignRound<Src> for (&mut Float, &mut Float)` are
        /// implemented with the returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Float};
        /// use rug::float::Round;
        /// use rug::ops::AssignRound;
        /// use std::cmp::Ordering;
        /// let phase = Float::with_val(53, 1.25);
        ///
        /// let (mut sinh, mut cosh) = (Float::new(53), Float::new(53));
        /// let sinh_cosh = phase.sinh_cosh_ref();
        /// (&mut sinh, &mut cosh).assign(sinh_cosh);
        /// let expected_sinh = 1.6019_f64;
        /// let expected_cosh = 1.8884_f64;
        /// assert!((sinh - expected_sinh).abs() < 0.0001);
        /// assert!((cosh - expected_cosh).abs() < 0.0001);
        ///
        /// // using 4 significant bits: sin = 1.625
        /// // using 4 significant bits: cos = 1.875
        /// let (mut sinh_4, mut cosh_4) = (Float::new(4), Float::new(4));
        /// let sinh_cosh = phase.sinh_cosh_ref();
        /// let (dir_sinh, dir_cosh) = (&mut sinh_4, &mut cosh_4)
        ///     .assign_round(sinh_cosh, Round::Nearest);
        /// assert_eq!(sinh_4, 1.625);
        /// assert_eq!(dir_sinh, Ordering::Greater);
        /// assert_eq!(cosh_4, 1.875);
        /// assert_eq!(dir_cosh, Ordering::Less);
        /// ```
        fn sinh_cosh_ref -> SinhCoshIncomplete;
    }
    math_op1_float! {
        mpfr::sech;
        /// Computes the hyperbolic secant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sech = f.sech();
        /// let expected = 0.5295_f64;
        /// assert!((sech - expected).abs() < 0.0001);
        /// ```
        fn sech();
        /// Computes the hyperbolic secant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.sech_mut();
        /// let expected = 0.5295_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn sech_mut;
        /// Computes the hyperbolic secant, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // sech(1.25) = 0.5295
        /// // using 4 significant bits: 0.5
        /// let dir = f.sech_round(Round::Nearest);
        /// assert_eq!(f, 0.5);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn sech_round;
        /// Computes the hyperbolic secant.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let sech = Float::with_val(53, f.sech_ref());
        /// let expected = 0.5295_f64;
        /// assert!((sech - expected).abs() < 0.0001);
        /// ```
        fn sech_ref -> SechIncomplete;
    }
    math_op1_float! {
        mpfr::csch;
        /// Computes the hyperbolic cosecant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let csch = f.csch();
        /// let expected = 0.6243_f64;
        /// assert!((csch - expected).abs() < 0.0001);
        /// ```
        fn csch();
        /// Computes the hyperbolic cosecant, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.csch_mut();
        /// let expected = 0.6243_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn csch_mut;
        /// Computes the hyperbolic cosecant, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // csch(1.25) = 0.6243
        /// // using 4 significant bits: 0.625
        /// let dir = f.csch_round(Round::Nearest);
        /// assert_eq!(f, 0.625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn csch_round;
        /// Computes the hyperbolic cosecant.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let csch = Float::with_val(53, f.csch_ref());
        /// let expected = 0.6243_f64;
        /// assert!((csch - expected).abs() < 0.0001);
        /// ```
        fn csch_ref -> CschIncomplete;
    }
    math_op1_float! {
        mpfr::coth;
        /// Computes the hyperbolic cotangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let coth = f.coth();
        /// let expected = 1.1789_f64;
        /// assert!((coth - expected).abs() < 0.0001);
        /// ```
        fn coth();
        /// Computes the hyperbolic cotangent, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.coth_mut();
        /// let expected = 1.1789_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn coth_mut;
        /// Computes the hyperbolic cotangent, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // coth(1.25) = 1.1789
        /// // using 4 significant bits: 1.125
        /// let dir = f.coth_round(Round::Nearest);
        /// assert_eq!(f, 1.125);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn coth_round;
        /// Computes the hyperbolic cotangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let coth = Float::with_val(53, f.coth_ref());
        /// let expected = 1.1789_f64;
        /// assert!((coth - expected).abs() < 0.0001);
        /// ```
        fn coth_ref -> CothIncomplete;
    }
    math_op1_float! {
        mpfr::asinh;
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let asinh = f.asinh();
        /// let expected = 1.0476_f64;
        /// assert!((asinh - expected).abs() < 0.0001);
        /// ```
        fn asinh();
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.asinh_mut();
        /// let expected = 1.0476_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn asinh_mut;
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // asinh(1.25) = 1.0476
        /// // using 4 significant bits: 1.0
        /// let dir = f.asinh_round(Round::Nearest);
        /// assert_eq!(f, 1.0);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn asinh_round;
        /// Computes the inverse hyperbolic sine.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let asinh = Float::with_val(53, f.asinh_ref());
        /// let expected = 1.0476_f64;
        /// assert!((asinh - expected).abs() < 0.0001);
        /// ```
        fn asinh_ref -> AsinhIncomplete;
    }
    math_op1_float! {
        mpfr::acosh;
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let acosh = f.acosh();
        /// let expected = 0.6931_f64;
        /// assert!((acosh - expected).abs() < 0.0001);
        /// ```
        fn acosh();
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.acosh_mut();
        /// let expected = 0.6931_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn acosh_mut;
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // acosh(1.25) = 0.6931
        /// // using 4 significant bits: 0.6875
        /// let dir = f.acosh_round(Round::Nearest);
        /// assert_eq!(f, 0.6875);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn acosh_round;
        /// Computes the inverse hyperbolic cosine
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let acosh = Float::with_val(53, f.acosh_ref());
        /// let expected = 0.6931_f64;
        /// assert!((acosh - expected).abs() < 0.0001);
        /// ```
        fn acosh_ref -> AcoshIncomplete;
    }
    math_op1_float! {
        mpfr::atanh;
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 0.75);
        /// let atanh = f.atanh();
        /// let expected = 0.9730_f64;
        /// assert!((atanh - expected).abs() < 0.0001);
        /// ```
        fn atanh();
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 0.75);
        /// f.atanh_mut();
        /// let expected = 0.9730_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn atanh_mut;
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 0.75);
        /// // atanh(0.75) = 0.9730
        /// // using 4 significant bits: 1.0
        /// let dir = f.atanh_round(Round::Nearest);
        /// assert_eq!(f, 1.0);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn atanh_round;
        /// Computes the inverse hyperbolic tangent.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 0.75);
        /// let atanh = Float::with_val(53, f.atanh_ref());
        /// let expected = 0.9730_f64;
        /// assert!((atanh - expected).abs() < 0.0001);
        /// ```
        fn atanh_ref -> AtanhIncomplete;
    }
    math_op0! {
        /// Computes the factorial of *n*.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// // 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
        /// let n = Float::factorial(10);
        /// let f = Float::with_val(53, n);
        /// assert_eq!(f, 3628800.0);
        /// ```
        fn factorial(n: u32) -> FactorialIncomplete;
    }

    /// Sets `self` to the factorial of *u*, rounding to the nearest.
    #[deprecated(since = "0.9.2",
                 note = "use `factorial` instead; `f.assign_factorial_u(u)` \
                         can be replaced with \
                         `f.assign(Float::factorial(u))`.")]
    #[inline]
    pub fn assign_factorial_u(&mut self, u: u32) {
        self.assign_round(Float::factorial(u), Round::Nearest);
    }

    /// Sets `self` to the factorial of *u*, applying the specified
    /// rounding method.
    #[deprecated(since = "0.9.2",
                 note = "use `factorial` instead; \
                         `f.assign_factorial_u_round(u, round)` can be \
                         replaced with \
                         `f.assign_round(Float::factorial(u), round))`.")]
    #[inline]
    pub fn assign_factorial_u_round(
        &mut self,
        u: u32,
        round: Round,
    ) -> Ordering {
        self.assign_round(Float::factorial(u), round)
    }

    math_op1_float! {
        mpfr::log1p;
        /// Computes the natural logarithm of one plus `self`, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let f = Float::with_val(53, 1.5 * two_to_m10);
        /// let ln_1p = f.ln_1p();
        /// let expected = 1.4989_f64 * two_to_m10;
        /// assert!((ln_1p - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn ln_1p();
        /// Computes the natural logarithm of one plus `self`, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let mut f = Float::with_val(53, 1.5 * two_to_m10);
        /// f.ln_1p_mut();
        /// let expected = 1.4989_f64 * two_to_m10;
        /// assert!((f - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn ln_1p_mut;
        /// Computes the natural logarithm of one plus `self`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let two_to_m10 = (-10f64).exp2();
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5 * two_to_m10);
        /// // ln_1p(1.5 * 2 ^ -10) = 1.4989 * 2 ^ -10
        /// // using 4 significant bits: 1.5 * 2 ^ -10
        /// let dir = f.ln_1p_round(Round::Nearest);
        /// assert_eq!(f, 1.5 * two_to_m10);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn ln_1p_round;
        /// Computes the natural logorithm of one plus the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let f = Float::with_val(53, 1.5 * two_to_m10);
        /// let ln_1p = Float::with_val(53, f.ln_1p_ref());
        /// let expected = 1.4989_f64 * two_to_m10;
        /// assert!((ln_1p - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn ln_1p_ref -> Ln1pIncomplete;
    }
    math_op1_float! {
        mpfr::expm1;
        /// Subtracts one from the exponential of `self`, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let f = Float::with_val(53, 1.5 * two_to_m10);
        /// let exp_m1 = f.exp_m1();
        /// let expected = 1.5011_f64 * two_to_m10;
        /// assert!((exp_m1 - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn exp_m1();
        /// Subtracts one from the exponential of `self`, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let mut f = Float::with_val(53, 1.5 * two_to_m10);
        /// f.exp_m1_mut();
        /// let expected = 1.5011_f64 * two_to_m10;
        /// assert!((f - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn exp_m1_mut;
        /// Subtracts one from the exponential of `self`, applying the
        /// specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// let two_to_m10 = (-10f64).exp2();
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.5 * two_to_m10);
        /// // exp_m1(1.5 * 2 ^ -10) = 1.5011 * 2 ^ -10
        /// // using 4 significant bits: 1.5 * 2 ^ -10
        /// let dir = f.exp_m1_round(Round::Nearest);
        /// assert_eq!(f, 1.5 * two_to_m10);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn exp_m1_round;
        /// Computes one less than the exponential of the
        /// value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let two_to_m10 = (-10f64).exp2();
        /// let f = Float::with_val(53, 1.5 * two_to_m10);
        /// let exp_m1 = Float::with_val(53, f.exp_m1_ref());
        /// let expected = 1.5011_f64 * two_to_m10;
        /// assert!((exp_m1 - expected).abs() < 0.0001 * two_to_m10);
        /// ```
        fn exp_m1_ref -> ExpM1Incomplete;
    }
    math_op1_float! {
        mpfr::eint;
        /// Computes the exponential integral, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let eint = f.eint();
        /// let expected = 2.5810_f64;
        /// assert!((eint - expected).abs() < 0.0001);
        /// ```
        fn eint();
        /// Computes the exponential integral, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.eint_mut();
        /// let expected = 2.5810_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn eint_mut;
        /// Computes the exponential integral, applying the specified
        /// rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // eint(1.25) = 2.5810
        /// // using 4 significant bits: 2.5
        /// let dir = f.eint_round(Round::Nearest);
        /// assert_eq!(f, 2.5);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn eint_round;
        /// Computes the exponential integral.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let eint = Float::with_val(53, f.eint_ref());
        /// let expected = 2.5810_f64;
        /// assert!((eint - expected).abs() < 0.0001);
        /// ```
        fn eint_ref -> EintIncomplete;
    }
    math_op1_float! {
        mpfr::li2;
        /// Computes the real part of the dilogarithm of `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let li2 = f.li2();
        /// let expected = 2.1902_f64;
        /// assert!((li2 - expected).abs() < 0.0001);
        /// ```
        fn li2();
        /// Computes the real part of the dilogarithm of `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.li2_mut();
        /// let expected = 2.1902_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn li2_mut;
        /// Computes the real part of the dilogarithm of `self`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // li2(1.25) = 2.1902
        /// // using 4 significant bits: 2.25
        /// let dir = f.li2_round(Round::Nearest);
        /// assert_eq!(f, 2.25);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn li2_round;
        /// Computes the real part of the dilogarithm of the
        /// value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let li2 = Float::with_val(53, f.li2_ref());
        /// let expected = 2.1902_f64;
        /// assert!((li2 - expected).abs() < 0.0001);
        /// ```
        fn li2_ref -> Li2Incomplete;
    }
    math_op1_float! {
        mpfr::gamma;
        /// Computes the value of the gamma function on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let gamma = f.gamma();
        /// let expected = 0.9064_f64;
        /// assert!((gamma - expected).abs() < 0.0001);
        /// ```
        fn gamma();
        /// Computes the value of the gamma function on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.gamma_mut();
        /// let expected = 0.9064_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn gamma_mut;
        /// Computes the value of the gamma function on `self`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // gamma(1.25) = 0.9064
        /// // using 4 significant bits: 0.9375
        /// let dir = f.gamma_round(Round::Nearest);
        /// assert_eq!(f, 0.9375);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn gamma_round;
        /// Computes the gamma function on the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let gamma = Float::with_val(53, f.gamma_ref());
        /// let expected = 0.9064_f64;
        /// assert!((gamma - expected).abs() < 0.0001);
        /// ```
        fn gamma_ref -> GammaIncomplete;
    }
    math_op2_float! {
        mpfr::gamma_inc;
        /// Computes the value of the upper incomplete gamma function
        /// on `self` and `x`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let x = Float::with_val(53, 2.5);
        /// let gamma_inc = f.gamma_inc(&x);
        /// let expected = 0.1116_f64;
        /// assert!((gamma_inc - expected).abs() < 0.0001);
        /// ```
        fn gamma_inc(x);
        /// Computes the value of the upper incomplete gamma function
        /// on `self`, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// let x = Float::with_val(53, 2.5);
        /// f.gamma_inc_mut(&x);
        /// let expected = 0.1116_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn gamma_inc_mut;
        /// Computes the value of the upper incomplete gamma function
        /// on `self`, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// let x = Float::with_val(53, 2.5);
        /// // gamma_inc(1.25, 2.5) = 0.1116
        /// // using 4 significant bits: 0.109375
        /// let dir = f.gamma_inc_round(&x, Round::Nearest);
        /// assert_eq!(f, 0.109375);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn gamma_inc_round;
        /// Computes the upper incomplete gamma function on the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let x = Float::with_val(53, 2.5);
        /// let gamma_inc = Float::with_val(53, f.gamma_inc_ref(&x));
        /// let expected = 0.1116_f64;
        /// assert!((gamma_inc - expected).abs() < 0.0001);
        /// ```
        fn gamma_inc_ref -> GammaIncIncomplete;
    }
    math_op1_float! {
        mpfr::lngamma;
        /// Computes the logarithm of the gamma function on `self`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let ln_gamma = f.ln_gamma();
        /// let expected = -0.0983_f64;
        /// assert!((ln_gamma - expected).abs() < 0.0001);
        /// ```
        fn ln_gamma();
        /// Computes the logarithm of the gamma function on `self`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.ln_gamma_mut();
        /// let expected = -0.0983_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn ln_gamma_mut;
        /// Computes the logarithm of the gamma function on `self`,
        /// applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // ln_gamma(1.25) = -0.0983
        /// // using 4 significant bits: -0.1015625
        /// let dir = f.ln_gamma_round(Round::Nearest);
        /// assert_eq!(f, -0.1015625);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn ln_gamma_round;
        /// Computes the logarithm of the gamma function on
        /// the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let ln_gamma = Float::with_val(53, f.ln_gamma_ref());
        /// let expected = -0.0983_f64;
        /// assert!((ln_gamma - expected).abs() < 0.0001);
        /// ```
        fn ln_gamma_ref -> LnGammaIncomplete;
    }

    /// Computes the logarithm of the absolute value of the gamma
    /// function on `self`, rounding to the nearest.
    ///
    /// Returns `Ordering::Less` if the gamma function is negative, or
    /// `Ordering::Greater` if the gamma function is positive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Constant;
    /// use std::cmp::Ordering;
    ///
    /// // gamma of 1/2 is sqrt(pi)
    /// let ln_gamma_64 = Float::with_val(64, Constant::Pi).sqrt().ln();
    ///
    /// let f = Float::with_val(53, 0.5);
    /// let (ln_gamma, sign) = f.ln_abs_gamma();
    /// // gamma of 1/2 is positive
    /// assert_eq!(sign, Ordering::Greater);
    /// // check to 53 significant bits
    /// assert_eq!(ln_gamma, Float::with_val(53, &ln_gamma_64));
    /// ```
    ///
    /// If the gamma function is negative, the sign returned is
    /// `Ordering::Less`.
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Constant;
    /// use std::cmp::Ordering;
    ///
    /// // gamma of -1/2 is -2 * sqrt(pi)
    /// let abs_gamma_64 = Float::with_val(64, Constant::Pi).sqrt() * 2u32;
    /// let ln_gamma_64 = abs_gamma_64.ln();
    ///
    /// let f = Float::with_val(53, -0.5);
    /// let (ln_gamma, sign) = f.ln_abs_gamma();
    /// // gamma of -1/2 is negative
    /// assert_eq!(sign, Ordering::Less);
    /// // check to 53 significant bits
    /// assert_eq!(ln_gamma, Float::with_val(53, &ln_gamma_64));
    /// ```
    #[inline]
    pub fn ln_abs_gamma(mut self) -> (Self, Ordering) {
        let sign = self.ln_abs_gamma_round(Round::Nearest).0;
        (self, sign)
    }

    /// Computes the logarithm of the absolute value of the gamma
    /// function on `self`, rounding to the nearest.
    ///
    /// Returns `Ordering::Less` if the gamma function is negative, or
    /// `Ordering::Greater` if the gamma function is positive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Constant;
    /// use std::cmp::Ordering;
    ///
    /// // gamma of -1/2 is -2 * sqrt(pi)
    /// let abs_gamma_64 = Float::with_val(64, Constant::Pi).sqrt() * 2u32;
    /// let ln_gamma_64 = abs_gamma_64.ln();
    ///
    /// let mut f = Float::with_val(53, -0.5);
    /// let sign = f.ln_abs_gamma_mut();
    /// // gamma of -1/2 is negative
    /// assert_eq!(sign, Ordering::Less);
    /// // check to 53 significant bits
    /// assert_eq!(f, Float::with_val(53, &ln_gamma_64));
    /// ```
    #[inline]
    pub fn ln_abs_gamma_mut(&mut self) -> Ordering {
        self.ln_abs_gamma_round(Round::Nearest).0
    }

    /// Computes the logarithm of the absolute value of the gamma
    /// function on `self`, applying the specified rounding method.
    ///
    /// The returned tuple contains:
    ///
    /// 1. The logarithm of the absolute value of the gamma function.
    /// 2. The rounding direction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::{Constant, Round};
    /// use std::cmp::Ordering;
    ///
    /// // gamma of -1/2 is -2 * sqrt(pi)
    /// let abs_gamma_64 = Float::with_val(64, Constant::Pi).sqrt() * 2u32;
    /// let ln_gamma_64 = abs_gamma_64.ln();
    ///
    /// let mut f = Float::with_val(53, -0.5);
    /// let (sign, dir) = f.ln_abs_gamma_round(Round::Nearest);
    /// // gamma of -1/2 is negative
    /// assert_eq!(sign, Ordering::Less);
    /// // check is correct to 53 significant bits
    /// let (check, check_dir) =
    ///     Float::with_val_round(53, &ln_gamma_64, Round::Nearest);
    /// assert_eq!(f, check);
    /// assert_eq!(dir, check_dir);
    /// ```
    #[inline]
    pub fn ln_abs_gamma_round(&mut self, round: Round) -> (Ordering, Ordering) {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let ret = unsafe {
            mpfr::lgamma(
                self.inner_mut(),
                sign_ptr,
                self.inner(),
                raw_round(round),
            )
        };
        let sign_ord = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        (sign_ord, ordering1(ret))
    }

    /// Computes the logarithm of the absolute value of the gamma
    /// function on `val`.
    ///
    /// `AssignRound<Src> for (Float, Ordering)` and
    /// `AssignRound<Src> for (&mut Float, &mut Ordering)` are
    /// implemented with the returned object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::float::Constant;
    /// use std::cmp::Ordering;
    ///
    /// let neg1_2 = Float::with_val(53, -0.5);
    /// // gamma of -1/2 is -2 * sqrt(pi)
    /// let abs_gamma_64 = Float::with_val(64, Constant::Pi).sqrt() * 2u32;
    /// let ln_gamma_64 = abs_gamma_64.ln();
    ///
    /// // Assign rounds to the nearest
    /// let r = neg1_2.ln_abs_gamma_ref();
    /// let (mut f, mut sign) = (Float::new(53), Ordering::Equal);
    /// (&mut f, &mut sign).assign(r);
    /// // gamma of -1/2 is negative
    /// assert_eq!(sign, Ordering::Less);
    /// // check to 53 significant bits
    /// assert_eq!(f, Float::with_val(53, &ln_gamma_64));
    /// ```
    #[inline]
    pub fn ln_abs_gamma_ref(&self) -> LnAbsGammaIncomplete {
        LnAbsGammaIncomplete { ref_self: self }
    }

    math_op1_float! {
        mpfr::digamma;
        /// Computes the value of the Digamma function on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let digamma = f.digamma();
        /// let expected = -0.2275_f64;
        /// assert!((digamma - expected).abs() < 0.0001);
        /// ```
        fn digamma();
        /// Computes the value of the Digamma function on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.digamma_mut();
        /// let expected = -0.2275_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn digamma_mut;
        /// Computes the value of the Digamma function on `self`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // digamma(1.25) = -0.2275
        /// // using 4 significant bits: -0.234375
        /// let dir = f.digamma_round(Round::Nearest);
        /// assert_eq!(f, -0.234375);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn digamma_round;
        /// Computes the Digamma function on the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let digamma = Float::with_val(53, f.digamma_ref());
        /// let expected = -0.2275_f64;
        /// assert!((digamma - expected).abs() < 0.0001);
        /// ```
        fn digamma_ref -> DigammaIncomplete;
    }
    math_op1_float! {
        mpfr::zeta;
        /// Computes the value of the Riemann Zeta function on `self`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let zeta = f.zeta();
        /// let expected = 4.5951_f64;
        /// assert!((zeta - expected).abs() < 0.0001);
        /// ```
        fn zeta();
        /// Computes the value of the Riemann Zeta function on `self`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.zeta_mut();
        /// let expected = 4.5951_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn zeta_mut;
        /// Computes the value of the Riemann Zeta function on `self`,
        /// applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // zeta(1.25) = 4.5951
        /// // using 4 significant bits: 4.5
        /// let dir = f.zeta_round(Round::Nearest);
        /// assert_eq!(f, 4.5);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn zeta_round;
        /// Computes the Riemann Zeta function on the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let zeta = Float::with_val(53, f.zeta_ref());
        /// let expected = 4.5951_f64;
        /// assert!((zeta - expected).abs() < 0.0001);
        /// ```
        fn zeta_ref -> ZetaIncomplete;
    }
    math_op0! {
        /// Computes the Riemann Zeta function on *u*.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let z = Float::zeta_u(3);
        /// let f = Float::with_val(53, z);
        /// let expected = 1.2021_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn zeta_u(u: u32) -> ZetaUIncomplete;
    }

    /// Sets `self` to the value of the Riemann Zeta function on *u*,
    /// rounding to the nearest.
    #[deprecated(since = "0.9.2",
                 note = "use `zeta_u` instead; `f.assign_zeta_u(u)` can be \
                         replaced with `f.assign(Float::zeta_u(u))`.")]
    #[inline]
    pub fn assign_zeta_u(&mut self, u: u32) {
        self.assign_round(Float::zeta_u(u), Round::Nearest);
    }

    /// Sets `self` to the value of the Riemann Zeta function on *u*,
    /// applying the specified rounding method.
    #[deprecated(since = "0.9.2",
                 note = "use `zeta_u` instead; \
                         `f.assign_zeta_u_round(u, round)` can be replaced \
                         with `f.assign_round(Float::zeta_u(u), round)`.")]
    #[inline]
    pub fn assign_zeta_u_round(&mut self, u: u32, round: Round) -> Ordering {
        self.assign_round(Float::zeta_u(u), round)
    }

    math_op1_float! {
        mpfr::erf;
        /// Computes the value of the error function, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let erf = f.erf();
        /// let expected = 0.9229_f64;
        /// assert!((erf - expected).abs() < 0.0001);
        /// ```
        fn erf();
        /// Computes the value of the error function, rounding to the
        /// nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.erf_mut();
        /// let expected = 0.9229_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn erf_mut;
        /// Computes the value of the error function, applying the
        /// specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // erf(1.25) = 0.9229
        /// // using 4 significant bits: 0.9375
        /// let dir = f.erf_round(Round::Nearest);
        /// assert_eq!(f, 0.9375);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn erf_round;
        /// Computes the error function.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let erf = Float::with_val(53, f.erf_ref());
        /// let expected = 0.9229_f64;
        /// assert!((erf - expected).abs() < 0.0001);
        /// ```
        fn erf_ref -> ErfIncomplete;
    }
    math_op1_float! {
        mpfr::erfc;
        /// Computes the value of the complementary error function,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let erfc = f.erfc();
        /// let expected = 0.0771_f64;
        /// assert!((erfc - expected).abs() < 0.0001);
        /// ```
        fn erfc();
        /// Computes the value of the complementary error function,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.erfc_mut();
        /// let expected = 0.0771_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn erfc_mut;
        /// Computes the value of the complementary error function,
        /// applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // erfc(1.25) = 0.0771
        /// // using 4 significant bits: 0.078125
        /// let dir = f.erfc_round(Round::Nearest);
        /// assert_eq!(f, 0.078125);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn erfc_round;
        /// Computes the complementary error function.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let erfc = Float::with_val(53, f.erfc_ref());
        /// let expected = 0.0771_f64;
        /// assert!((erfc - expected).abs() < 0.0001);
        /// ```
        fn erfc_ref -> ErfcIncomplete;
    }
    math_op1_float! {
        mpfr::j0;
        /// Computes the value of the first kind Bessel function of
        /// order 0, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j0 = f.j0();
        /// let expected = 0.6459_f64;
        /// assert!((j0 - expected).abs() < 0.0001);
        /// ```
        fn j0();
        /// Computes the value of the first kind Bessel function of
        /// order 0, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.j0_mut();
        /// let expected = 0.6459_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn j0_mut;
        /// Computes the value of the first kind Bessel function of
        /// order 0, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // j0(1.25) = 0.6459
        /// // using 4 significant bits: 0.625
        /// let dir = f.j0_round(Round::Nearest);
        /// assert_eq!(f, 0.625);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn j0_round;
        /// Computes the first kind Bessel function of order 0.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j0 = Float::with_val(53, f.j0_ref());
        /// let expected = 0.6459_f64;
        /// assert!((j0 - expected).abs() < 0.0001);
        /// ```
        fn j0_ref -> J0Incomplete;
    }
    math_op1_float! {
        mpfr::j1;
        /// Computes the value of the first kind Bessel function of
        /// order 1, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j1 = f.j1();
        /// let expected = 0.5106_f64;
        /// assert!((j1 - expected).abs() < 0.0001);
        /// ```
        fn j1();
        /// Computes the value of the first kind Bessel function of
        /// order 1, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.j1_mut();
        /// let expected = 0.5106_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn j1_mut;
        /// Computes the value of the first kind Bessel function of
        /// order 1, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // j1(1.25) = 0.5106
        /// // using 4 significant bits: 0.5
        /// let dir = f.j1_round(Round::Nearest);
        /// assert_eq!(f, 0.5);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn j1_round;
        /// Computes the first kind Bessel function of order 1.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j1 = Float::with_val(53, f.j1_ref());
        /// let expected = 0.5106_f64;
        /// assert!((j1 - expected).abs() < 0.0001);
        /// ```
        fn j1_ref -> J1Incomplete;
    }
    math_op1_float! {
        xmpfr::jn;
        /// Computes the value of the first kind Bessel function of
        /// order *n*, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j2 = f.jn(2);
        /// let expected = 0.1711_f64;
        /// assert!((j2 - expected).abs() < 0.0001);
        /// ```
        fn jn(n: i32);
        /// Computes the value of the first kind Bessel function of
        /// order *n*, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.jn_mut(2);
        /// let expected = 0.1711_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn jn_mut;
        /// Computes the value of the first kind Bessel function of
        /// order *n*, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // j2(1.25) = 0.1711
        /// // using 4 significant bits: 0.171875
        /// let dir = f.jn_round(2, Round::Nearest);
        /// assert_eq!(f, 0.171875);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn jn_round;
        /// Computes the first kind Bessel function of order *n*.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let j2 = Float::with_val(53, f.jn_ref(2));
        /// let expected = 0.1711_f64;
        /// assert!((j2 - expected).abs() < 0.0001);
        /// ```
        fn jn_ref -> JnIncomplete;
    }
    math_op1_float! {
        mpfr::y0;
        /// Computes the value of the second kind Bessel function of
        /// order 0, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y0 = f.y0();
        /// let expected = 0.2582_f64;
        /// assert!((y0 - expected).abs() < 0.0001);
        /// ```
        fn y0();
        /// Computes the value of the second kind Bessel function of
        /// order 0, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.y0_mut();
        /// let expected = 0.2582_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn y0_mut;
        /// Computes the value of the second kind Bessel function of
        /// order 0, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // y0(1.25) = 0.2582
        /// // using 4 significant bits: 0.25
        /// let dir = f.y0_round(Round::Nearest);
        /// assert_eq!(f, 0.25);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn y0_round;
        /// Computes the second kind Bessel function of order 0.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y0 = Float::with_val(53, f.y0_ref());
        /// let expected = 0.2582_f64;
        /// assert!((y0 - expected).abs() < 0.0001);
        /// ```
        fn y0_ref -> Y0Incomplete;
    }
    math_op1_float! {
        mpfr::y1;
        /// Computes the value of the second kind Bessel function of
        /// order 1, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y1 = f.y1();
        /// let expected = -0.5844_f64;
        /// assert!((y1 - expected).abs() < 0.0001);
        /// ```
        fn y1();
        /// Computes the value of the second kind Bessel function of
        /// order 1, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.y1_mut();
        /// let expected = -0.5844_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn y1_mut;
        /// Computes the value of the second kind Bessel function of
        /// order 1, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // y1(1.25) = -0.5844
        /// // using 4 significant bits: -0.5625
        /// let dir = f.y1_round(Round::Nearest);
        /// assert_eq!(f, -0.5625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn y1_round;
        /// Computes the second kind Bessel function of order 1.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y1 = Float::with_val(53, f.y1_ref());
        /// let expected = -0.5844_f64;
        /// assert!((y1 - expected).abs() < 0.0001);
        /// ```
        fn y1_ref -> Y1Incomplete;
    }
    math_op1_float! {
        xmpfr::yn;
        /// Computes the value of the second kind Bessel function of
        /// order *n*, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y2 = f.yn(2);
        /// let expected = -1.1932_f64;
        /// assert!((y2 - expected).abs() < 0.0001);
        /// ```
        fn yn(n: i32);
        /// Computes the value of the second kind Bessel function of
        /// order *n*, rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.yn_mut(2);
        /// let expected = -1.1932_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn yn_mut;
        /// Computes the value of the second kind Bessel function of
        /// order *n*, applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // y2(1.25) = -1.1932
        /// // using 4 significant bits: -1.25
        /// let dir = f.yn_round(2, Round::Nearest);
        /// assert_eq!(f, -1.25);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn yn_round;
        /// Computes the second kind Bessel function of order *n*.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let y2 = Float::with_val(53, f.yn_ref(2));
        /// let expected = -1.1932_f64;
        /// assert!((y2 - expected).abs() < 0.0001);
        /// ```
        fn yn_ref -> YnIncomplete;
    }
    math_op2_float! {
        mpfr::agm;
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// let agm = f.agm(&g);
        /// let expected = 2.3295_f64;
        /// assert!((agm - expected).abs() < 0.0001);
        /// ```
        fn agm(other);
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// rounding to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// f.agm_mut(&g);
        /// let expected = 2.3295_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn agm_mut;
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// applying the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// let g = Float::with_val(4, 3.75);
        /// // agm(1.25, 3.75) = 2.3295
        /// // using 4 significant bits: 2.25
        /// let dir = f.agm_round(&g, Round::Nearest);
        /// assert_eq!(f, 2.25);
        /// assert_eq!(dir, Ordering::Less);
        /// ```
        fn agm_round;
        /// Computes the arithmetic-geometric mean.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// let agm = Float::with_val(53, f.agm_ref(&g));
        /// let expected = 2.3295_f64;
        /// assert!((agm - expected).abs() < 0.0001);
        /// ```
        fn agm_ref -> AgmIncomplete;
    }
    math_op2_float! {
        mpfr::hypot;
        /// Computes the Euclidean norm of `self` and `other`, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// let hypot = f.hypot(&g);
        /// let expected = 3.9528_f64;
        /// assert!((hypot - expected).abs() < 0.0001);
        /// ```
        fn hypot(other);
        /// Computes the Euclidean norm of `self` and `other`, rounding to
        /// the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// f.hypot_mut(&g);
        /// let expected = 3.9528_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn hypot_mut;
        /// Computes the Euclidean norm of `self` and `other`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// let g = Float::with_val(4, 3.75);
        /// // hypot(1.25) = 3.9528
        /// // using 4 significant bits: 4.0
        /// let dir = f.hypot_round(&g, Round::Nearest);
        /// assert_eq!(f, 4.0);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn hypot_round;
        /// Computes the Euclidean norm.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let g = Float::with_val(53, 3.75);
        /// let hypot = Float::with_val(53, f.hypot_ref(&g));
        /// let expected = 3.9528_f64;
        /// assert!((hypot - expected).abs() < 0.0001);
        /// ```
        fn hypot_ref -> HypotIncomplete;
    }
    math_op1_float! {
        mpfr::ai;
        /// Computes the value of the Airy function Ai on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let ai = f.ai();
        /// let expected = 0.0996_f64;
        /// assert!((ai - expected).abs() < 0.0001);
        /// ```
        fn ai();
        /// Computes the value of the Airy function Ai on `self`, rounding
        /// to the nearest.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f = Float::with_val(53, 1.25);
        /// f.ai_mut();
        /// let expected = 0.0996_f64;
        /// assert!((f - expected).abs() < 0.0001);
        /// ```
        fn ai_mut;
        /// Computes the value of the Airy function Ai on `self`, applying
        /// the specified rounding method.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // Use only 4 bits of precision to show rounding.
        /// let mut f = Float::with_val(4, 1.25);
        /// // ai(1.25) = 0.0996
        /// // using 4 significant bits: 0.1015625
        /// let dir = f.ai_round(Round::Nearest);
        /// assert_eq!(f, 0.1015625);
        /// assert_eq!(dir, Ordering::Greater);
        /// ```
        fn ai_round;
        /// Computes the Airy function Ai on the value.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f = Float::with_val(53, 1.25);
        /// let ai = Float::with_val(53, f.ai_ref());
        /// let expected = 0.0996_f64;
        /// assert!((ai - expected).abs() < 0.0001);
        /// ```
        fn ai_ref -> AiIncomplete;
    }
    math_op1_no_round! {
        mpfr::rint_ceil, raw_round;
        /// Rounds up to the next higher integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let ceil1 = f1.ceil();
        /// assert_eq!(ceil1, -23);
        /// let f2 = Float::with_val(53, 23.75);
        /// let ceil2 = f2.ceil();
        /// assert_eq!(ceil2, 24);
        /// ```
        fn ceil();
        /// Rounds up to the next higher integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// f1.ceil_mut();
        /// assert_eq!(f1, -23);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// f2.ceil_mut();
        /// assert_eq!(f2, 24);
        /// ```
        fn ceil_mut;
        /// Rounds up to the next higher integer. The result may be
        /// rounded again when assigned to the target.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let ceil1 = Float::with_val(53, f1.ceil_ref());
        /// assert_eq!(ceil1, -23);
        /// let f2 = Float::with_val(53, 23.75);
        /// let ceil2 = Float::with_val(53, f2.ceil_ref());
        /// assert_eq!(ceil2, 24);
        /// ```
        fn ceil_ref -> CeilIncomplete;
    }
    math_op1_no_round! {
        mpfr::rint_floor, raw_round;
        /// Rounds down to the next lower integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let floor1 = f1.floor();
        /// assert_eq!(floor1, -24);
        /// let f2 = Float::with_val(53, 23.75);
        /// let floor2 = f2.floor();
        /// assert_eq!(floor2, 23);
        /// ```
        fn floor();
        /// Rounds down to the next lower integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// f1.floor_mut();
        /// assert_eq!(f1, -24);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// f2.floor_mut();
        /// assert_eq!(f2, 23);
        /// ```
        fn floor_mut;
        /// Rounds down to the next lower integer. The result may be
        /// rounded again when assigned to the target.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let floor1 = Float::with_val(53, f1.floor_ref());
        /// assert_eq!(floor1, -24);
        /// let f2 = Float::with_val(53, 23.75);
        /// let floor2 = Float::with_val(53, f2.floor_ref());
        /// assert_eq!(floor2, 23);
        /// ```
        fn floor_ref -> FloorIncomplete;
    }
    math_op1_no_round! {
        mpfr::rint_round, raw_round;
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let round1 = f1.round();
        /// assert_eq!(round1, -24);
        /// let f2 = Float::with_val(53, 23.75);
        /// let round2 = f2.round();
        /// assert_eq!(round2, 24);
        /// ```
        fn round();
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// f1.round_mut();
        /// assert_eq!(f1, -24);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// f2.round_mut();
        /// assert_eq!(f2, 24);
        /// ```
        fn round_mut;
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero. The result may be rounded again when
        /// assigned to the target.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let round1 = Float::with_val(53, f1.round_ref());
        /// assert_eq!(round1, -24);
        /// let f2 = Float::with_val(53, 23.75);
        /// let round2 = Float::with_val(53, f2.round_ref());
        /// assert_eq!(round2, 24);
        /// ```
        ///
        /// Double rounding may happen when assigning to a target with
        /// a precision less than the number of significant bits for
        /// the truncated integer.
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use rug::ops::AssignRound;
        /// let f = Float::with_val(53, 6.5);
        /// // 6.5 (binary 110.1) is rounded to 7 (binary 111)
        /// let r = f.round_ref();
        /// // use only 2 bits of precision in destination
        /// let mut dst = Float::new(2);
        /// // 7 (binary 111) is rounded to 8 (binary 1000) by
        /// // round-even rule in order to store in 2-bit Float, even
        /// // though 6 (binary 110) is closer to original 6.5).
        /// dst.assign_round(r, Round::Nearest);
        /// assert_eq!(dst, 8);
        /// ```
       fn round_ref -> RoundIncomplete;
    }
    math_op1_no_round! {
        mpfr::rint_roundeven, raw_round;
        /// Rounds to the nearest integer, rounding half-way cases to
        /// even.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, 23.5);
        /// let round1 = f1.round_even();
        /// assert_eq!(round1, 24);
        /// let f2 = Float::with_val(53, 24.5);
        /// let round2 = f2.round_even();
        /// assert_eq!(round2, 24);
        /// ```
        fn round_even();
        /// Rounds to the nearest integer, rounding half-way cases to
        /// even.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, 23.5);
        /// f1.round_even_mut();
        /// assert_eq!(f1, 24);
        /// let mut f2 = Float::with_val(53, 24.5);
        /// f2.round_even_mut();
        /// assert_eq!(f2, 24);
        /// ```
        fn round_even_mut;
        /// Rounds to the nearest integer, rounding half-way cases to
        /// even. The result may be rounded again when assigned to the
        /// target.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, 23.5);
        /// let round1 = Float::with_val(53, f1.round_even_ref());
        /// assert_eq!(round1, 24);
        /// let f2 = Float::with_val(53, 24.5);
        /// let round2 = Float::with_val(53, f2.round_even_ref());
        /// assert_eq!(round2, 24);
        /// ```
       fn round_even_ref -> RoundEvenIncomplete;
    }
    math_op1_no_round! {
        mpfr::rint_trunc, raw_round;
        /// Rounds to the next integer towards zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let trunc1 = f1.trunc();
        /// assert_eq!(trunc1, -23);
        /// let f2 = Float::with_val(53, 23.75);
        /// let trunc2 = f2.trunc();
        /// assert_eq!(trunc2, 23);
        /// ```
        fn trunc();
        /// Rounds to the next integer towards zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// f1.trunc_mut();
        /// assert_eq!(f1, -23);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// f2.trunc_mut();
        /// assert_eq!(f2, 23);
        /// ```
        fn trunc_mut;
        /// Rounds to the next integer towards zero. The result may be
        /// rounded again when assigned to the target.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let trunc1 = Float::with_val(53, f1.trunc_ref());
        /// assert_eq!(trunc1, -23);
        /// let f2 = Float::with_val(53, 23.75);
        /// let trunc2 = Float::with_val(53, f2.trunc_ref());
        /// assert_eq!(trunc2, 23);
        /// ```
        fn trunc_ref -> TruncIncomplete;
    }
    math_op1_no_round! {
        mpfr::frac, raw_round;
        /// Gets the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let fract1 = f1.fract();
        /// assert_eq!(fract1, -0.75);
        /// let f2 = Float::with_val(53, 23.75);
        /// let fract2 = f2.fract();
        /// assert_eq!(fract2, 0.75);
        /// ```
        fn fract();
        /// Gets the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// f1.fract_mut();
        /// assert_eq!(f1, -0.75);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// f2.fract_mut();
        /// assert_eq!(f2, 0.75);
        /// ```
        fn fract_mut;
        /// Gets the fractional part of the number.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let fract1 = Float::with_val(53, f1.fract_ref());
        /// assert_eq!(fract1, -0.75);
        /// let f2 = Float::with_val(53, 23.75);
        /// let fract2 = Float::with_val(53, f2.fract_ref());
        /// assert_eq!(fract2, 0.75);
        /// ```
        fn fract_ref -> FractIncomplete;
    }
    math_op1_2_float! {
        mpfr::modf;
        /// Gets the integer and fractional parts of the number,
        /// rounding to the nearest.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let f1 = Float::with_val(53, -23.75);
        /// let (trunc1, fract1) = f1.trunc_fract(Float::new(53));
        /// assert_eq!(trunc1, -23);
        /// assert_eq!(fract1, -0.75);
        /// let f2 = Float::with_val(53, 23.75);
        /// let (trunc2, fract2) = f2.trunc_fract(Float::new(53));
        /// assert_eq!(trunc2, 23);
        /// assert_eq!(fract2, 0.75);
        /// ```
        fn trunc_fract(fract);
        /// Gets the integer and fractional parts of the number,
        /// rounding to the nearest.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// let mut f1 = Float::with_val(53, -23.75);
        /// let mut fract1 = Float::new(53);
        /// f1.trunc_fract_mut(&mut fract1);
        /// assert_eq!(f1, -23);
        /// assert_eq!(fract1, -0.75);
        /// let mut f2 = Float::with_val(53, 23.75);
        /// let mut fract2 = Float::new(53);
        /// f2.trunc_fract_mut(&mut fract2);
        /// assert_eq!(f2, 23);
        /// assert_eq!(fract2, 0.75);
        /// ```
        fn trunc_fract_mut;
        /// Gets the integer and fractional parts of the number,
        /// applying the specified rounding method.
        ///
        /// The first element of the returned tuple of rounding
        /// directions is always `Ordering::Equal`, as truncating a
        /// value in place will always be exact.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Float;
        /// use rug::float::Round;
        /// use std::cmp::Ordering;
        /// // 0.515625 in binary is 0.100001
        /// let mut f1 = Float::with_val(53, -23.515625);
        /// let mut fract1 = Float::new(4);
        /// let dir1 = f1.trunc_fract_round(&mut fract1, Round::Nearest);
        /// assert_eq!(f1, -23);
        /// assert_eq!(fract1, -0.5);
        /// assert_eq!(dir1, (Ordering::Equal, Ordering::Greater));
        /// let mut f2 = Float::with_val(53, 23.515625);
        /// let mut fract2 = Float::new(4);
        /// let dir2 = f2.trunc_fract_round(&mut fract2, Round::Nearest);
        /// assert_eq!(f2, 23);
        /// assert_eq!(fract2, 0.5);
        /// assert_eq!(dir2, (Ordering::Equal, Ordering::Less));
        /// ```
        fn trunc_fract_round;
        /// Gets the integer and fractional parts of the number.
        ///
        /// `AssignRound<Src> for Float` is implemented with the
        /// returned object as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Float};
        /// let f1 = Float::with_val(53, -23.75);
        /// let r1 = f1.trunc_fract_ref();
        /// let (mut trunc1, mut fract1) = (Float::new(53), Float::new(53));
        /// (&mut trunc1, &mut fract1).assign(r1);
        /// assert_eq!(trunc1, -23);
        /// assert_eq!(fract1, -0.75);
        /// let f2 = Float::with_val(53, -23.75);
        /// let r2 = f2.trunc_fract_ref();
        /// let (mut trunc2, mut fract2) = (Float::new(53), Float::new(53));
        /// (&mut trunc2, &mut fract2).assign(r2);
        /// assert_eq!(trunc2, -23);
        /// assert_eq!(fract2, -0.75);
        /// ```
        fn trunc_fract_ref -> TruncFractIncomplete;
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the range 0 ≤ *x* < 1.
    ///
    /// This is equivalent to generating a random integer in the range
    /// 0 ≤ *x* < 2<sup>*p*</sup>, where 2<sup>*p*</sup> is two raised
    /// to the power of the precision, and then dividing the integer
    /// by 2<sup>*p*</sup>. The smallest non-zero result will thus be
    /// 2<sup>−<i>p</i></sup>, and will only have one bit set. In the
    /// smaller possible results, many bits will be zero, and not all
    /// the precision will be used.
    ///
    /// There is a corner case where the generated random number is
    /// converted to NaN: if the precision is very large, the
    /// generated random number could have an exponent less than the
    /// allowed minimum exponent, and NaN is used to indicate this.
    /// For this to occur in practice, the minimum exponent has to be
    /// set to have a very small magnitude using the low-level MPFR
    /// interface, or the random number generator has to be designed
    /// specifically to trigger this case.
    ///
    /// `Assign<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Float};
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut f = Float::new(2);
    /// f.assign(Float::random_bits(&mut rand));
    /// assert!(f == 0.0 || f == 0.25 || f == 0.5 || f == 0.75);
    /// println!("0.0 ≤ {} < 1.0", f);
    /// ```
    #[inline]
    pub fn random_bits<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomBitsIncomplete<'a, 'b> {
        RandomBitsIncomplete { rng }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the range 0 ≤ *x* < 1.
    #[deprecated(since = "0.9.2",
                 note = "use `random_bits` instead; \
                         `f.assign_random_bits(rng)` can be replaced with \
                         `f.assign(Float::random_bits(rng))`, and testing the \
                         result can be replaced with testing for NaN.")]
    #[inline]
    pub fn assign_random_bits(
        &mut self,
        rng: &mut RandState,
    ) -> Result<(), ()> {
        self.assign(Float::random_bits(rng));
        if self.is_nan() {
            Err(())
        } else {
            Ok(())
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the continuous range 0 ≤ *x* < 1.
    ///
    /// The result can be rounded up to be equal to one. Unlike the
    /// [`random_bits`](#method.random_bits) method which generates a
    /// discrete random number at intervals depending on the
    /// precision, this method is equivalent to generating a
    /// continuous random number with infinite precision and then
    /// rounding the result. This means that even the smaller numbers
    /// will be using all the available precision bits, and rounding
    /// is performed in all cases, not in some corner case.
    ///
    /// Rounding directions for generated random numbers cannot be
    /// `Ordering::Equal`, as the random numbers generated can be
    /// considered to have infinite precision before rounding.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let f = Float::with_val(2, Float::random_cont(&mut rand));
    /// // The significand is either 0b10 or 0b11
    /// assert!(
    ///     f == 1.0 || f == 0.75 || f == 0.5 || f == 0.375 || f == 0.25
    ///         || f <= 0.1875
    /// );
    /// ```
    #[inline]
    pub fn random_cont<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomCont<'a, 'b> {
        RandomCont { rng }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the continuous range 0 ≤ *x* < 1,
    /// and rounds to the nearest.
    #[deprecated(since = "0.9.2",
                 note = "use `random_cont` instead; \
                         `f.assign_random_cont(rng)` can be replaced with \
                         `f.assign(Float::random_cont(rng))`.")]
    #[inline]
    pub fn assign_random_cont(&mut self, rng: &mut RandState) {
        self.assign_round(Float::random_cont(rng), Round::Nearest);
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the continous range 0 ≤ *x* < 1,
    /// and applies the specified rounding method.
    #[deprecated(since = "0.9.2",
                 note = "use `random_cont` instead; \
                         `f.assign_random_cont_round(rng)` can be replaced \
                         with \
                         `f.assign_round(Float::random_cont(rng), round)`.")]
    #[inline]
    pub fn assign_random_cont_round(
        &mut self,
        rng: &mut RandState,
        round: Round,
    ) -> Ordering {
        self.assign_round(Float::random_cont(rng), round)
    }

    #[cfg(feature = "rand")]
    /// Generates a random number according to a standard normal
    /// Gaussian distribution, rounding to the nearest.
    ///
    /// Rounding directions for generated random numbers cannot be
    /// `Ordering::Equal`, as the random numbers generated can be
    /// considered to have infinite precision before rounding.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let f = Float::with_val(53, Float::random_normal(&mut rand));
    /// println!("Normal random number: {}", f);
    /// ```
    #[inline]
    pub fn random_normal<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomNormal<'a, 'b> {
        RandomNormal { rng }
    }

    #[cfg(feature = "rand")]
    /// Generates two random numbers according to a standard normal
    /// Gaussian distribution, rounding to the nearest.
    ///
    /// If `other` is `None`, only one value is generated.
    #[deprecated(since = "0.9.2",
                 note = "use `random_normal` instead; if `other` is `None` \
                         then `f.assign_random_gaussian(other, rng)` can be \
                         replaced with `f.assign(Float::random_normal(rng))`; \
                         if `other` is `Some(&mut g)` instead then \
                         `g.assign(Float::random_normal(rng))` can be added.")]
    #[inline]
    pub fn assign_random_gaussian(
        &mut self,
        other: Option<&mut Self>,
        rng: &mut RandState,
    ) {
        self.assign_round(Float::random_normal(rng), Round::Nearest);
        if let Some(other) = other {
            other.assign_round(Float::random_normal(rng), Round::Nearest);
        }
    }

    #[cfg(feature = "rand")]
    /// Generates two random numbers according to a standard normal
    /// Gaussian distribution, applying the specified rounding method.
    ///
    /// If `other` is `None`, only one value is generated.
    #[deprecated(since = "0.9.2",
                 note = "use `random_normal` instead; if `other` is `None` \
                         then \
                         `f.assign_random_gaussian_round(other, rng, round)` \
                         can be replaced with \
                         `f.assign_round(Float::random_normal(rng), round)`; \
                         if `other` is `Some(&mut g)` instead then \
                         `g.assign_round(Float::random_normal(rng), round)` \
                         can be added.")]
    #[inline]
    pub fn assign_random_gaussian_round(
        &mut self,
        other: Option<&mut Self>,
        rng: &mut RandState,
        round: Round,
    ) -> (Ordering, Ordering) {
        let first = self.assign_round(Float::random_normal(rng), round);
        let second = if let Some(other) = other {
            other.assign_round(Float::random_normal(rng), round)
        } else {
            Ordering::Equal
        };
        (first, second)
    }

    #[cfg(feature = "rand")]
    /// Generates a random number according to an exponential
    /// distribution with mean one, rounding to the nearest.
    ///
    /// Rounding directions for generated random numbers cannot be
    /// `Ordering::Equal`, as the random numbers generated can be
    /// considered to have infinite precision before rounding.
    ///
    /// `AssignRound<Src> for Float` is implemented with the returned
    /// object as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let f = Float::with_val(53, Float::random_exp(&mut rand));
    /// println!("Exponential random number: {}", f);
    /// ```
    #[inline]
    pub fn random_exp<'a, 'b: 'a>(
        rng: &'a mut RandState<'b>,
    ) -> RandomExp<'a, 'b> {
        RandomExp { rng }
    }
}

#[derive(Debug)]
pub struct SumIncomplete<'a, I>
where
    I: Iterator<Item = &'a Float>,
{
    values: I,
}

impl<'a, I> AssignRound<SumIncomplete<'a, I>> for Float
where
    I: Iterator<Item = &'a Self>,
{
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(
        &mut self,
        src: SumIncomplete<'a, I>,
        round: Round,
    ) -> Ordering {
        let refs = src.values
            .map(|r| r.inner() as *const mpfr_t)
            .collect::<Vec<_>>();
        let tab = refs.as_ptr() as *const *mut mpfr_t;
        let n = cast(refs.len());
        let ret =
            unsafe { mpfr::sum(self.inner_mut(), tab, n, raw_round(round)) };
        ordering1(ret)
    }
}

impl<'a, I> Add<SumIncomplete<'a, I>> for Float
where
    I: Iterator<Item = &'a Self>,
{
    type Output = Self;
    #[inline]
    fn add(mut self, rhs: SumIncomplete<'a, I>) -> Self {
        self.add_assign_round(rhs, Round::Nearest);
        self
    }
}

impl<'a, I> AddAssign<SumIncomplete<'a, I>> for Float
where
    I: Iterator<Item = &'a Self>,
{
    #[inline]
    fn add_assign(&mut self, rhs: SumIncomplete<'a, I>) {
        self.add_assign_round(rhs, Round::Nearest);
    }
}

impl<'a, I> AddAssignRound<SumIncomplete<'a, I>> for Float
where
    I: Iterator<Item = &'a Self>,
{
    type Round = Round;
    type Ordering = Ordering;
    fn add_assign_round(
        &mut self,
        src: SumIncomplete<'a, I>,
        round: Round,
    ) -> Ordering {
        let mut refs = match src.values.size_hint() {
            (_, None) => Vec::new(),
            (_, Some(upper)) => Vec::with_capacity(upper + 1),
        };
        refs.push(self.inner() as *const mpfr_t);
        refs.extend(src.values.map(|r| r.inner() as *const mpfr_t));
        let tab = refs.as_ptr() as *const *mut mpfr_t;
        let n = cast(refs.len());
        let ret =
            unsafe { mpfr::sum(self.inner_mut(), tab, n, raw_round(round)) };
        ordering1(ret)
    }
}

ref_math_op1_float! { mpfr::sqr; struct SquareIncomplete {} }
ref_math_op1_float! { mpfr::sqrt; struct SqrtIncomplete {} }
ref_math_op0_float! { mpfr::sqrt_ui; struct SqrtUIncomplete { u: u32 } }
ref_math_op1_float! { mpfr::rec_sqrt; struct RecipSqrtIncomplete {} }
ref_math_op1_float! { mpfr::cbrt; struct CbrtIncomplete {} }
ref_math_op1_float! { mpfr::rootn_ui; struct RootIncomplete { k: u32 } }
ref_math_op1_float! { mpfr::abs; struct AbsIncomplete {} }
ref_math_op1_float! { xmpfr::signum; struct SignumIncomplete {} }

#[derive(Debug)]
pub struct ClampIncomplete<'a, Min, Max>
where
    Float: PartialOrd<Min>
        + PartialOrd<Max>
        + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
        + AssignRound<&'a Max, Round = Round, Ordering = Ordering>,
    Min: 'a,
    Max: 'a,
{
    ref_self: &'a Float,
    min: &'a Min,
    max: &'a Max,
}

impl<'a, Min, Max> AssignRound<ClampIncomplete<'a, Min, Max>> for Float
where
    Self: PartialOrd<Min>
        + PartialOrd<Max>
        + AssignRound<&'a Min, Round = Round, Ordering = Ordering>
        + AssignRound<&'a Max, Round = Round, Ordering = Ordering>,
    Min: 'a,
    Max: 'a,
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: ClampIncomplete<'a, Min, Max>,
        round: Round,
    ) -> Ordering {
        if src.ref_self.lt(src.min) {
            let dir = self.assign_round(src.min, round);
            if (*self).gt(src.max) {
                let dir2 = self.assign_round(src.max, round);
                assert!(
                    dir == dir2 && !(*self).lt(src.min),
                    "minimum larger than maximum"
                );
                dir
            } else {
                dir
            }
        } else if src.ref_self.gt(src.max) {
            let dir = self.assign_round(src.max, round);
            if (*self).lt(src.min) {
                let dir2 = self.assign_round(src.min, round);
                assert!(
                    dir == dir2 && !(*self).gt(src.max),
                    "minimum larger than maximum"
                );
                dir
            } else {
                dir
            }
        } else {
            self.assign_round(src.ref_self, round)
        }
    }
}

ref_math_op1_float! { xmpfr::recip; struct RecipIncomplete {} }
ref_math_op2_float! { mpfr::min; struct MinIncomplete { other } }
ref_math_op2_float! { mpfr::max; struct MaxIncomplete { other } }
ref_math_op2_float! { mpfr::dim; struct PositiveDiffIncomplete { other } }
ref_math_op1_float! { mpfr::log; struct LnIncomplete {} }
ref_math_op0_float! { mpfr::log_ui; struct LnUIncomplete { u: u32 } }
ref_math_op1_float! { mpfr::log2; struct Log2Incomplete {} }
ref_math_op1_float! { mpfr::log10; struct Log10Incomplete {} }
ref_math_op1_float! { mpfr::exp; struct ExpIncomplete {} }
ref_math_op1_float! { mpfr::exp2; struct Exp2Incomplete {} }
ref_math_op1_float! { mpfr::exp10; struct Exp10Incomplete {} }
ref_math_op1_float! { mpfr::sin; struct SinIncomplete {} }
ref_math_op1_float! { mpfr::cos; struct CosIncomplete {} }
ref_math_op1_float! { mpfr::tan; struct TanIncomplete {} }
ref_math_op1_2_float! { mpfr::sin_cos; struct SinCosIncomplete {} }
ref_math_op1_float! { mpfr::sec; struct SecIncomplete {} }
ref_math_op1_float! { mpfr::csc; struct CscIncomplete {} }
ref_math_op1_float! { mpfr::cot; struct CotIncomplete {} }
ref_math_op1_float! { mpfr::acos; struct AcosIncomplete {} }
ref_math_op1_float! { mpfr::asin; struct AsinIncomplete {} }
ref_math_op1_float! { mpfr::atan; struct AtanIncomplete {} }
ref_math_op2_float! { mpfr::atan2; struct Atan2Incomplete { x } }
ref_math_op1_float! { mpfr::cosh; struct CoshIncomplete {} }
ref_math_op1_float! { mpfr::sinh; struct SinhIncomplete {} }
ref_math_op1_float! { mpfr::tanh; struct TanhIncomplete {} }
ref_math_op1_2_float! { mpfr::sinh_cosh; struct SinhCoshIncomplete {} }
ref_math_op1_float! { mpfr::sech; struct SechIncomplete {} }
ref_math_op1_float! { mpfr::csch; struct CschIncomplete {} }
ref_math_op1_float! { mpfr::coth; struct CothIncomplete {} }
ref_math_op1_float! { mpfr::acosh; struct AcoshIncomplete {} }
ref_math_op1_float! { mpfr::asinh; struct AsinhIncomplete {} }
ref_math_op1_float! { mpfr::atanh; struct AtanhIncomplete {} }
ref_math_op0_float! { mpfr::fac_ui; struct FactorialIncomplete { n: u32 } }
ref_math_op1_float! { mpfr::log1p; struct Ln1pIncomplete {} }
ref_math_op1_float! { mpfr::expm1; struct ExpM1Incomplete {} }
ref_math_op1_float! { mpfr::eint; struct EintIncomplete {} }
ref_math_op1_float! { mpfr::li2; struct Li2Incomplete {} }
ref_math_op1_float! { mpfr::gamma; struct GammaIncomplete {} }
ref_math_op2_float! { mpfr::gamma_inc; struct GammaIncIncomplete { x } }
ref_math_op1_float! { mpfr::lngamma; struct LnGammaIncomplete {} }

pub struct LnAbsGammaIncomplete<'a> {
    ref_self: &'a Float,
}

impl<'a, 'b, 'c> AssignRound<LnAbsGammaIncomplete<'a>>
    for (&'b mut Float, &'c mut Ordering)
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: LnAbsGammaIncomplete<'a>,
        round: Round,
    ) -> Ordering {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let ret = unsafe {
            mpfr::lgamma(
                self.0.inner_mut(),
                sign_ptr,
                src.ref_self.inner(),
                raw_round(round),
            )
        };
        *self.1 = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        ordering1(ret)
    }
}

ref_math_op1_float! { mpfr::digamma; struct DigammaIncomplete {} }
ref_math_op1_float! { mpfr::zeta; struct ZetaIncomplete {} }
ref_math_op0_float! { mpfr::zeta_ui; struct ZetaUIncomplete { u: u32 } }
ref_math_op1_float! { mpfr::erf; struct ErfIncomplete {} }
ref_math_op1_float! { mpfr::erfc; struct ErfcIncomplete {} }
ref_math_op1_float! { mpfr::j0; struct J0Incomplete {} }
ref_math_op1_float! { mpfr::j1; struct J1Incomplete {} }
ref_math_op1_float! { xmpfr::jn; struct JnIncomplete { n: i32 } }
ref_math_op1_float! { mpfr::y0; struct Y0Incomplete {} }
ref_math_op1_float! { mpfr::y1; struct Y1Incomplete {} }
ref_math_op1_float! { xmpfr::yn; struct YnIncomplete { n: i32 } }
ref_math_op2_float! { mpfr::agm; struct AgmIncomplete { other } }
ref_math_op2_float! { mpfr::hypot; struct HypotIncomplete { other } }
ref_math_op1_float! { mpfr::ai; struct AiIncomplete {} }
ref_math_op1_float! { mpfr::rint_ceil; struct CeilIncomplete {} }
ref_math_op1_float! { mpfr::rint_floor; struct FloorIncomplete {} }
ref_math_op1_float! { mpfr::rint_round; struct RoundIncomplete {} }
ref_math_op1_float! { mpfr::rint_roundeven; struct RoundEvenIncomplete {} }
ref_math_op1_float! { mpfr::rint_trunc; struct TruncIncomplete {} }
ref_math_op1_float! { mpfr::frac; struct FractIncomplete {} }
ref_math_op1_2_float! { mpfr::modf; struct TruncFractIncomplete {} }

#[cfg(feature = "rand")]
pub struct RandomBitsIncomplete<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a, 'c> Assign<RandomBitsIncomplete<'a, 'b>> for Float {
    #[inline]
    fn assign(&mut self, src: RandomBitsIncomplete<'a, 'b>) {
        unsafe {
            let err = mpfr::urandomb(self.inner_mut(), src.rng.inner_mut());
            assert_eq!(self.is_nan(), err != 0);
        }
    }
}

#[cfg(feature = "rand")]
pub struct RandomCont<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignRound<RandomCont<'a, 'b>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: RandomCont<'a, 'b>,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::urandom(
                self.inner_mut(),
                src.rng.inner_mut(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

#[cfg(feature = "rand")]
pub struct RandomNormal<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignRound<RandomNormal<'a, 'b>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: RandomNormal<'a, 'b>,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::nrandom(
                self.inner_mut(),
                src.rng.inner_mut(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

#[cfg(feature = "rand")]
pub struct RandomExp<'a, 'b: 'a> {
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignRound<RandomExp<'a, 'b>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: RandomExp<'a, 'b>,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::erandom(
                self.inner_mut(),
                src.rng.inner_mut(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

#[derive(Debug)]
pub struct BorrowFloat<'a> {
    inner: mpfr_t,
    phantom: PhantomData<&'a Float>,
}

impl<'a> Deref for BorrowFloat<'a> {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

pub(crate) fn req_chars(
    f: &Float,
    radix: i32,
    precision: Option<usize>,
    extra: usize,
) -> usize {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let size = if f.is_zero() {
        3
    } else if f.is_infinite() || f.is_nan() {
        if radix > 10 {
            5
        } else {
            3
        }
    } else {
        let digits = precision.map(|x| if x == 1 { 2 } else { x }).unwrap_or(0);
        let num_chars = if digits == 0 {
            // According to mpfr_get_str documentation, we need
            // 1 + ceil(p / log2(radix)), but in some cases, it is 1 more.
            // p is prec - 1 if radix is a power of two, or prec otherwise.
            let ur = radix as u32;
            let pdiv = if ur.is_power_of_two() {
                f64::from(f.prec() - 1) / f64::from(31 - ur.leading_zeros())
            } else {
                f64::from(f.prec()) / f64::from(ur).log2()
            };
            cast::<_, usize>(pdiv.ceil())
                .checked_add(2)
                .expect("overflow")
        } else {
            digits
        };
        // allow for exponent, including prefix like "e-"
        let exp_chars: f64 = cast(8 * mem::size_of::<mpfr::exp_t>());
        let exp_chars = (exp_chars * 2.0f64.log10()).ceil();
        let exp_chars: usize = cast(exp_chars);
        // one for '.' and two for exponent prefix like "e-"
        num_chars.checked_add(exp_chars + 3).expect("overflow")
    };
    let size_extra = size.checked_add(extra).expect("overflow");
    if f.is_sign_negative() {
        size_extra.checked_add(1).expect("overflow")
    } else {
        size_extra
    }
}

pub(crate) fn append_to_string(
    s: &mut String,
    f: &Float,
    radix: i32,
    precision: Option<usize>,
    round: Round,
    to_upper: bool,
) {
    // add 1 for nul
    let size = req_chars(f, radix, precision, 1);
    s.reserve(size);
    if f.is_zero() {
        s.push_str(if f.is_sign_negative() { "-0.0" } else { "0.0" });
        return;
    }
    if f.is_infinite() {
        s.push_str(match (radix > 10, f.is_sign_negative()) {
            (false, false) => "inf",
            (false, true) => "-inf",
            (true, false) => "@inf@",
            (true, true) => "-@inf@",
        });
        return;
    }
    if f.is_nan() {
        s.push_str(match (radix > 10, f.is_sign_negative()) {
            (false, false) => "NaN",
            (false, true) => "-NaN",
            (true, false) => "@NaN@",
            (true, true) => "-@NaN@",
        });
        return;
    }
    let orig_len = s.len();
    let digits = precision.map(|x| if x == 1 { 2 } else { x }).unwrap_or(0);
    let mut exp: mpfr::exp_t;
    unsafe {
        let bytes = s.as_mut_vec();
        let start = bytes.as_mut_ptr().offset(orig_len as isize);
        exp = mem::uninitialized();
        // write numbers starting at offset 1, to leave room for '.'
        mpfr::get_str(
            start.offset(1) as *mut c_char,
            &mut exp,
            cast(radix),
            digits,
            f.inner(),
            raw_round(round),
        );
        let added = slice::from_raw_parts_mut(start, size);
        let added1 = *added.get_unchecked(1);
        if added1 == b'-' {
            let added2 = *added.get_unchecked(2);
            *added.get_unchecked_mut(0) = b'-';
            *added.get_unchecked_mut(1) = added2;
            *added.get_unchecked_mut(2) = b'.';
        } else {
            *added.get_unchecked_mut(0) = added1;
            *added.get_unchecked_mut(1) = b'.';
        }
        // search for nul after setting added[0], not before
        let nul_index = added.iter().position(|&x| x == 0).unwrap();
        if to_upper {
            added[0..nul_index].make_ascii_uppercase();
        }
        bytes.set_len(orig_len + nul_index);
    }
    let exp = exp.checked_sub(1).expect("overflow");
    if exp != 0 {
        s.push(if radix > 10 {
            '@'
        } else if to_upper {
            'E'
        } else {
            'e'
        });
        use std::fmt::Write;
        write!(s, "{}", exp).unwrap();
    }
}

#[derive(Clone, Debug)]
pub enum ParseIncomplete {
    CString { c_string: CString, radix: i32 },
    Special(Special),
    NegNan,
}

impl AssignRound<ParseIncomplete> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: ParseIncomplete, round: Round) -> Ordering {
        let (c_string, radix) = match src {
            ParseIncomplete::CString { c_string, radix } => (c_string, radix),
            ParseIncomplete::Special(special) => {
                self.assign(special);
                return Ordering::Equal;
            }
            ParseIncomplete::NegNan => {
                self.assign(Special::Nan);
                self.neg_assign();
                return Ordering::Equal;
            }
        };
        let mut c_str_end: *const c_char = ptr::null();
        let ret = unsafe {
            mpfr::strtofr(
                self.inner_mut(),
                c_string.as_ptr(),
                &mut c_str_end as *mut _ as *mut *mut c_char,
                cast(radix),
                raw_round(round),
            )
        };
        let nul = c_string.as_bytes_with_nul().last().unwrap() as *const _
            as *const c_char;
        assert_eq!(c_str_end, nul);
        ordering1(ret)
    }
}

macro_rules! parse_error {
    ($kind: expr) => {
        Err(ParseFloatError { kind: $kind })
    };
}

fn parse(
    mut bytes: &[u8],
    radix: i32,
) -> Result<ParseIncomplete, ParseFloatError> {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let bradix: u8 = cast(radix);
    let small_bound = b'a' - 10 + bradix;
    let capital_bound = b'A' - 10 + bradix;
    let digit_bound = b'0' + bradix;

    bytes = misc::trim_start(bytes);
    bytes = misc::trim_end(bytes);
    if bytes.is_empty() {
        parse_error!(ParseErrorKind::NoDigits)?;
    }

    let mut has_sign = false;
    let mut has_minus = false;
    if bytes[0] == b'+' || bytes[0] == b'-' {
        has_sign = true;
        has_minus = bytes[0] == b'-';
        bytes = misc::trim_start(&bytes[1..]);
        if bytes.is_empty() {
            parse_error!(ParseErrorKind::NoDigits)?;
        }
    }

    if let Some(special) = parse_special(bytes, radix, has_minus) {
        return special;
    }

    let mut v = Vec::with_capacity(bytes.len() + 2);
    if has_minus {
        v.push(b'-');
    }
    let mut has_digits = false;
    let mut has_point = false;
    let mut exp = false;
    for &b in bytes {
        let b = if radix <= 10 && (b == b'e' || b == b'E') {
            b'@'
        } else {
            b
        };
        let valid_digit = match b {
            b'.' if exp => parse_error!(ParseErrorKind::PointInExp)?,
            b'.' if has_point => parse_error!(ParseErrorKind::TooManyPoints)?,
            b'.' => {
                v.push(b'.');
                has_point = true;
                continue;
            }
            b'@' if exp => parse_error!(ParseErrorKind::TooManyExp)?,
            b'@' if !has_digits => {
                parse_error!(ParseErrorKind::SignifNoDigits)?
            }
            b'@' => {
                v.push(b'@');
                exp = true;
                has_sign = false;
                has_digits = false;
                continue;
            }
            b'+' if exp && !has_sign && !has_digits => {
                has_sign = true;
                continue;
            }
            b'-' if exp && !has_sign && !has_digits => {
                v.push(b'-');
                has_sign = true;
                continue;
            }
            b'_' if has_digits => continue,
            b' ' | b'\t' | b'\n' | 0x0b | 0x0c | 0x0d => continue,

            b'0'...b'9' => exp || b < digit_bound,
            b'a'...b'z' => !exp && b < small_bound,
            b'A'...b'Z' => !exp && b < capital_bound,
            _ => false,
        };
        if !valid_digit {
            parse_error!(ParseErrorKind::InvalidDigit)?;
        }
        v.push(b);
        has_digits = true;
    }
    if !has_digits {
        if exp {
            parse_error!(ParseErrorKind::ExpNoDigits)?;
        } else {
            parse_error!(ParseErrorKind::NoDigits)?;
        }
    }
    // we've only added checked bytes, so we know there are no nuls
    let c_string = unsafe { CString::from_vec_unchecked(v) };
    Ok(ParseIncomplete::CString { c_string, radix })
}

fn parse_special(
    bytes: &[u8],
    radix: i32,
    negative: bool,
) -> Option<Result<ParseIncomplete, ParseFloatError>> {
    let small = if radix <= 10 { Some(()) } else { None };

    let inf10: &[&[u8]] = &[b"inf", b"infinity"];
    let inf: &[&[u8]] = &[b"@inf@", b"@infinity@"];
    if let Some(after_inf) = small
        .and_then(|()| misc::skip_lcase_match(bytes, inf10))
        .or_else(|| misc::skip_lcase_match(bytes, inf))
        .map(misc::trim_start)
    {
        if !after_inf.is_empty() {
            return Some(parse_error!(ParseErrorKind::InvalidDigit));
        }
        return if negative {
            Some(Ok(ParseIncomplete::Special(Special::NegInfinity)))
        } else {
            Some(Ok(ParseIncomplete::Special(Special::Infinity)))
        };
    }

    let nan10: &[&[u8]] = &[b"nan", b"+nan"];
    let nan: &[&[u8]] = &[b"@nan@", b"+@nan@"];
    if let Some(after_nan) = small
        .and_then(|()| misc::skip_lcase_match(bytes, nan10))
        .or_else(|| misc::skip_lcase_match(bytes, nan))
        .map(misc::trim_start)
    {
        let trailing = if let Some(after_extra) =
            skip_nan_extra(after_nan).map(misc::trim_start)
        {
            after_extra
        } else {
            after_nan
        };
        if !trailing.is_empty() {
            return Some(parse_error!(ParseErrorKind::InvalidDigit));
        }
        return if negative {
            Some(Ok(ParseIncomplete::NegNan))
        } else {
            Some(Ok(ParseIncomplete::Special(Special::Nan)))
        };
    }
    None
}

// If bytes starts with nan extras e.g. b"(stuff)", return bytes with
// the match skipped.
fn skip_nan_extra(bytes: &[u8]) -> Option<&[u8]> {
    let mut iter = bytes.iter().enumerate();
    match iter.next() {
        Some((_, &b'(')) => {}
        _ => return None,
    }
    for (i, &b) in iter {
        match b {
            b')' => return Some(&bytes[i + 1..]),
            b'0'...b'9'
            | b'a'...b'z'
            | b'A'...b'Z'
            | b'_'
            | b' '
            | b'\t'
            | b'\n'
            | 0x0b
            | 0x0c
            | 0x0d => {}
            _ => return None,
        }
    }
    None
}

/// A validated string that can always be converted to a
/// [`Float`](../struct.Float.html).
#[allow(deprecated)]
#[deprecated(since = "0.10.0",
             note = "use the `Float::parse_radix` method instead of \
                     `Float::valid_str_radix`, and if for example you were \
                     storing the returned object in a struct, convert into a \
                     `Float` before storing.")]
#[derive(Clone, Debug)]
pub struct ValidFloat<'a> {
    inner: ParseIncomplete,
    phantom: PhantomData<&'a ()>,
}

#[allow(deprecated)]
impl<'a> AssignRound<ValidFloat<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: ValidFloat<'a>, round: Round) -> Ordering {
        self.assign_round(src.inner, round)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing a `Float`.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::ParseFloatError;
/// // This string is not a floating-point number.
/// let s = "something completely different (_!_!_)";
/// let error: ParseFloatError = match Float::parse_radix(s, 4) {
///     Ok(_) => unreachable!(),
///     Err(error) => error,
/// };
/// println!("Parse error: {:?}", error);
/// ```
pub struct ParseFloatError {
    kind: ParseErrorKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

fn ieee_storage_bits_for_prec(prec: u32) -> Option<u32> {
    match prec {
        11 => return Some(16),
        24 => return Some(32),
        53 => return Some(64),
        _ => {}
    }
    if prec < 113 {
        return None;
    }
    // p = k - round(4 log2 k) + 13
    // k = p - 13 + round(4 log2 k)
    // But we only need to find an approximation for k with error < 16,
    // and log2 k - log2 p < 1/5 when p ≥ 113.
    // estimate = p - 13 + 4 * log2 p
    // log2 p is approximately 31.5 - prec.leading_zeros()
    let estimate = prec - 4 * prec.leading_zeros() + 113;
    // k must be a multiple of 32
    let k = (estimate + 16) & !31;
    let p = k - cast::<_, u32>((f64::from(k).log2() * 4.0).round()) + 13;
    if p == prec {
        Some(k)
    } else {
        None
    }
}

impl Inner for Float {
    type Output = mpfr_t;
    #[inline]
    fn inner(&self) -> &mpfr_t {
        &self.inner
    }
}

impl InnerMut for Float {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut mpfr_t {
        &mut self.inner
    }
}
