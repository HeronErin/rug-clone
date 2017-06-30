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

use {Assign, AssignRound};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use ext::mpfr as xmpfr;
use float::SmallFloat;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use inner::{Inner, InnerMut};
use ops::{AddAssignRound, AddFrom, AddFromRound, DivAssignRound, DivFrom,
          DivFromRound, MulAssignRound, MulFrom, MulFromRound, NegAssign, Pow,
          PowAssign, PowAssignRound, PowFrom, PowFromRound, SubAssignRound,
          SubFrom, SubFromRound};
#[cfg(feature = "rand")]
use rand::RandState;
use std::{i32, u32};
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ops::{Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Neg,
               Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
use std::ptr;
use std::slice;

/// Returns the minimum value for the exponent.
///
/// # Examples
///
/// ```rust
/// use rug::float;
/// println!("Minimum exponent is {}", float::exp_min());
/// ```
#[inline]
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
///
/// # Examples
///
/// ```rust
/// use rug::float;
/// println!("Maximum exponent is {}", float::exp_max());
/// ```
#[inline]
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
///
/// # Examples
///
/// ```rust
/// use rug::float;
/// println!("Minimum precision is {}", float::prec_min());
/// ```
#[inline]
pub fn prec_min() -> u32 {
    mpfr::PREC_MIN as u32
}

/// Returns the maximum value for the precision.
///
/// # Examples
///
/// ```rust
/// use rug::float;
/// println!("Maximum precision is {}", float::prec_max());
/// ```
#[inline]
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
///
/// When rounding to the nearest, if the number to be rounded is
/// exactly between two representable numbers, it is rounded to
/// the even one, that is, the one with the least significant bit
/// set to zero.
///
/// # Examples
///
/// ```rust
/// use rug::{AssignRound, Float};
/// use rug::float::Round;
/// let mut f4 = Float::new(4);
/// f4.assign_round(10.4, Round::Nearest);
/// assert_eq!(f4, 10);
/// f4.assign_round(10.6, Round::Nearest);
/// assert_eq!(f4, 11);
/// f4.assign_round(-10.7, Round::Zero);
/// assert_eq!(f4, -10);
/// f4.assign_round(10.3, Round::AwayFromZero);
/// assert_eq!(f4, 11);
/// ```
///
/// Rounding to the nearest will round numbers exactly between two
/// representable numbers to the even one.
///
/// ```rust
/// use rug::{AssignRound, Float};
/// use rug::float::Round;
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
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Round {
    /// Round towards the nearest.
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

impl Default for Round {
    #[inline]
    fn default() -> Round {
        Round::Nearest
    }
}

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

/// The available floating-point constants.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::Constant;
///
/// let log2 = Float::with_val(53, Constant::Log2);
/// let pi = Float::with_val(53, Constant::Pi);
/// let euler = Float::with_val(53, Constant::Euler);
/// let catalan = Float::with_val(53, Constant::Catalan);
///
/// assert_eq!(log2.to_string_radix(10, Some(5)), "6.9315e-1");
/// assert_eq!(pi.to_string_radix(10, Some(5)), "3.1416");
/// assert_eq!(euler.to_string_radix(10, Some(5)), "5.7722e-1");
/// assert_eq!(catalan.to_string_radix(10, Some(5)), "9.1597e-1");
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Constant {
    /// The logarithm of two, 0.693...
    Log2,
    /// The value of pi, 3.141...
    Pi,
    /// Euler’s constant, 0.577...
    Euler,
    /// Catalan’s constant, 0.915...
    Catalan,
}

/// Special floating-point values.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::Constant;
///
/// let log2 = Float::with_val(53, Constant::Log2);
/// let pi = Float::with_val(53, Constant::Pi);
/// let euler = Float::with_val(53, Constant::Euler);
/// let catalan = Float::with_val(53, Constant::Catalan);
///
/// assert_eq!(log2.to_string_radix(10, Some(5)), "6.9315e-1");
/// assert_eq!(pi.to_string_radix(10, Some(5)), "3.1416");
/// assert_eq!(euler.to_string_radix(10, Some(5)), "5.7722e-1");
/// assert_eq!(catalan.to_string_radix(10, Some(5)), "9.1597e-1");
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[inline]
fn ordering1(ord: c_int) -> Ordering {
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
/// There are two versions of most methods:
///
/// 1. The first rounds the returned or stored `Float` to the
///    [nearest](float/enum.Round.html#variant.Nearest) representable
///    value.
/// 2. The second applies the specified [rounding
///    method](float/enum.Round.html), and returns the rounding
///    direction:
///    * `Ordering::Less` if the returned/stored `Float` is less than
///      the exact result,
///    * `Ordering::Equal` if the returned/stored `Float` is equal to
///      the exact result,
///    * `Ordering::Greater` if the returned/stored `Float` is greater
///      than the exact result,
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
/// intermediate value that has to be assigned to a new `Float` value.
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
/// As a special case, when an intermediate value is obtained from
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
/// The following example is a translation of the [MPFR
/// sample](http://www.mpfr.org/sample.html) found on the MPFR
/// website. The program computes a lower bound on 1 + 1/1! + 1/2! + …
/// + 1/100! using 200-bit precision. The program writes:
///
/// `Sum is 2.7182818284590452353602874713526624977572470936999595749669131`
///
/// ```rust
/// extern crate rug;
/// use rug::{AssignRound, Float};
/// use rug::float::Round;
/// use rug::ops::{AddAssignRound, MulAssignRound};
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
pub struct Float {
    inner: mpfr_t,
}

impl Clone for Float {
    #[inline]
    fn clone(&self) -> Float {
        let mut ret = Float::new(self.prec());
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Float) {
        self.set_prec(source.prec());
        self.assign(source);
    }
}

impl Drop for Float {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            mpfr::clear(self.inner_mut());
        }
    }
}

impl Hash for Float {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner().exp.hash(state);
        if self.is_nan() || self.is_zero() {
            return;
        }
        self.inner().sign.hash(state);
        if self.is_infinite() {
            return;
        }
        let prec = self.prec();
        assert_eq!(prec as usize as u32, prec);
        let prec = prec as usize;
        let mut limbs = prec / gmp::LIMB_BITS as usize;
        // MPFR keeps unused bits set to zero, so use whole of last limb
        if prec % gmp::LIMB_BITS as usize > 0 {
            limbs += 1;
        };
        let slice = unsafe { slice::from_raw_parts(self.inner().d, limbs) };
        slice.hash(state);
    }
}

macro_rules! math_op1_float {
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
            Float, Round => Ordering;
            $func, rraw => ordering1;
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

macro_rules! ref_math_op1_float {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        ref_math_op1_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $(#[$attr_ref])*
            struct $Ref { $($param: $T),* }
        }
    }
}

macro_rules! math_op1_2_float {
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
            Float, Round => (Ordering, Ordering);
            $func, rraw => ordering2;
            $(#[$attr])*
            fn $method($rop $(, $param: $T)*);
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_mut])*
            fn $method_mut;
            $(#[$attr_ref])*
            fn $method_ref -> $Ref;
        }
    }
}

macro_rules! ref_math_op1_2_float {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
        ref_math_op1_2_round! {
            Float, Round => (Ordering, Ordering);
            $func, rraw => ordering2;
            $(#[$attr_ref])*
            struct $Ref { $($param: $T),* }
        }
    }
}

macro_rules! math_op2_float {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($op:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_round:meta])*
        fn $method_round:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        math_op2_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $(#[$attr])*
            fn $method($op $(, $param: $T)*);
            $(#[$attr_mut])*
            fn $method_mut;
            $(#[$attr_round])*
            fn $method_round;
            $(#[$attr_ref])*
            fn $method_ref -> $Ref;
        }
    }
}

macro_rules! ref_math_op2_float {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $op:ident $(, $param:ident: $T:ty),* }
    } => {
        ref_math_op2_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $(#[$attr_ref])*
            struct $Ref { $op $(, $param: $T)* }
        }
    }
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
    pub fn new(prec: u32) -> Float {
        let mut ret = Float::new_nan(prec);
        ret.assign(Special::Zero);
        ret
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
    pub fn with_val<T>(prec: u32, val: T) -> Float
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
    ) -> (Float, Ordering)
    where
        Float: AssignRound<T, Round = Round, Ordering = Ordering>,
    {
        let mut ret = Float::new_nan(prec);
        let ord = ret.assign_round(val, round);
        (ret, ord)
    }

    #[inline]
    fn new_nan(prec: u32) -> Float {
        assert!(
            prec >= prec_min() && prec <= prec_max(),
            "precision out of range"
        );
        unsafe {
            let mut ret: Float = mem::uninitialized();
            mpfr::init2(ret.inner_mut(), prec as mpfr::prec_t);
            ret
        }
    }

    /// Returns the precision.
    #[inline]
    pub fn prec(&self) -> u32 {
        unsafe { mpfr::get_prec(self.inner()) as u32 }
    }

    /// Sets the precision, rounding to the nearest.
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
    /// # Panics
    ///
    /// Panics if `prec` is out of the allowed range.
    #[inline]
    pub fn set_prec_round(&mut self, prec: u32, round: Round) -> Ordering {
        assert!(
            prec >= prec_min() && prec <= prec_max(),
            "precision out of range"
        );
        let ret = unsafe {
            mpfr::prec_round(
                self.inner_mut(),
                prec as mpfr::prec_t,
                rraw(round),
            )
        };
        ordering1(ret)
    }

    /// Parses a `Float` with the specified precision, rounding to the
    /// nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    #[inline]
    pub fn from_str(src: &str, prec: u32) -> Result<Float, ParseFloatError> {
        let mut f = Float::new_nan(prec);
        f.assign_str(src)?;
        Ok(f)
    }

    /// Parses a `Float` with the specified precision, applying the
    /// specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_round).
    #[inline]
    pub fn from_str_round(
        src: &str,
        prec: u32,
        round: Round,
    ) -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new_nan(prec);
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
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
        prec: u32,
    ) -> Result<Float, ParseFloatError> {
        let mut f = Float::new_nan(prec);
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
    #[inline]
    pub fn from_str_radix_round(
        src: &str,
        radix: i32,
        prec: u32,
        round: Round,
    ) -> Result<(Float, Ordering), ParseFloatError> {
        let mut f = Float::new_nan(prec);
        let ord = f.assign_str_radix_round(src, radix, round)?;
        Ok((f, ord))
    }

    /// Checks if a `Float` can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Float`. If this method returns
    /// an error, the other functions will return the same error.
    ///
    /// The string can start with an optional minus or plus sign.
    /// Whitespace is not allowed anywhere in the string, including in
    /// the beginning and end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    ///
    /// let valid1 = Float::valid_str_radix("12.23e-4", 4);
    /// let f1 = Float::with_val(53, valid1.unwrap());
    /// assert_eq!(f1, (2.0 + 4.0 * 1.0 + 0.25 * (2.0 + 0.25 * 3.0)) / 256.0);
    /// let valid2 = Float::valid_str_radix("12.yz@2", 36);
    /// let f2 = Float::with_val(53, valid2.unwrap());
    /// assert_eq!(f2, 35 + 36 * (34 + 36 * (2 + 36 * 1)));
    ///
    /// let invalid = Float::valid_str_radix("ffe-2", 16);
    /// let invalid_f = Float::from_str_radix("ffe-2", 16, 53);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidFloat, ParseFloatError> {
        use self::ParseFloatError as Error;
        use self::ParseErrorKind as Kind;

        let mut v = ValidFloat {
            poss: ValidPoss::Special(Special::Nan),
            radix: radix,
            exp_plus: None,
        };
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let bytes = src.as_bytes();
        let inf10: &[&[u8]] = &[b"inf", b"+inf", b"infinity", b"+infinity"];
        let inf: &[&[u8]] =
            &[b"@inf@", b"+@inf@", b"@infinity@", b"+@infinity@"];
        if (radix <= 10 && lcase_in(bytes, inf10)) || lcase_in(bytes, inf) {
            v.poss = ValidPoss::Special(Special::Infinity);
            return Ok(v);
        }
        let neg_inf10: &[&[u8]] = &[b"-inf", b"-infinity"];
        let neg_inf: &[&[u8]] = &[b"-@inf@", b"-@infinity@"];
        if (radix <= 10 && lcase_in(bytes, neg_inf10)) ||
            lcase_in(bytes, neg_inf)
        {
            v.poss = ValidPoss::Special(Special::MinusInfinity);
            return Ok(v);
        }
        let nan10: &[&[u8]] = &[b"nan", b"+nan", b"-nan"];
        let nan: &[&[u8]] = &[b"@nan@", b"+@nan@", b"-@nan@"];
        if (radix <= 10 && lcase_in(bytes, nan10)) || lcase_in(bytes, nan) {
            v.poss = ValidPoss::Special(Special::Nan);
            return Ok(v);
        }

        let mut iter = bytes.iter();
        let starts_with_plus = bytes.starts_with(&[b'+']);
        let starts_with_minus = bytes.starts_with(&[b'-']);
        if starts_with_plus || starts_with_minus {
            iter.next();
        }
        let mut got_digit = false;
        let mut got_point = false;
        let mut exp = false;
        let mut fresh_exp = false;
        for (i, b) in iter.enumerate() {
            if fresh_exp {
                fresh_exp = false;
                if *b == b'-' {
                    continue;
                }
                if *b == b'+' {
                    v.exp_plus = if starts_with_minus {
                        Some(i + 1)
                    } else {
                        Some(i)
                    };
                    continue;
                }
            }
            if *b == b'.' {
                if exp {
                    return Err(Error { kind: Kind::PointInExp });
                }
                if got_point {
                    return Err(Error { kind: Kind::TooManyPoints });
                }
                got_point = true;
                continue;
            }
            if (radix <= 10 && (*b == b'e' || *b == b'E')) || *b == b'@' {
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
            let digit = match *b {
                b'0'...b'9' => *b - b'0',
                b'a'...b'z' => *b - b'a' + 10,
                b'A'...b'Z' => *b - b'A' + 10,
                _ => Err(Error { kind: Kind::InvalidDigit })?,
            };
            if (!exp && digit >= radix as u8) || (exp && digit >= 10) {
                return Err(Error { kind: Kind::InvalidDigit });
            }
            got_digit = true;
        }
        if !got_digit && exp {
            return Err(Error { kind: Kind::ExpNoDigits });
        } else if !got_digit {
            return Err(Error { kind: Kind::NoDigits });
        }
        v.poss = if starts_with_plus {
            ValidPoss::Bytes(&bytes[1..])
        } else {
            ValidPoss::Bytes(bytes)
        };
        Ok(v)
    }

    #[cfg(feature = "integer")]
    /// Converts to an integer, rounding to the nearest.
    #[inline]
    pub fn to_integer(&self) -> Option<Integer> {
        self.to_integer_round(Round::Nearest).map(|x| x.0)
    }

    #[cfg(feature = "integer")]
    /// Converts to an integer, applying the specified rounding method.
    #[inline]
    pub fn to_integer_round(
        &self,
        round: Round,
    ) -> Option<(Integer, Ordering)> {
        if !self.is_finite() {
            return None;
        }
        let mut i = Integer::new();
        let ret =
            unsafe { mpfr::get_z(i.inner_mut(), self.inner(), rraw(round)) };
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
        let exp =
            unsafe { mpfr::get_z_2exp(i.inner_mut(), self.inner()) as i32 };
        Some((i, exp))
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
    /// let res = Float::from_str_round("0.0123456789", 35, Round::Down);
    /// let (f, f_rounding) = res.unwrap();
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
        self.to_integer_exp()
            .map(|(num, exp)| Rational::from(num) << exp)
    }

    /// Converts to an `i32`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    #[inline]
    pub fn to_i32_saturating(&self) -> Option<i32> {
        self.to_i32_saturating_round(Round::Nearest)
    }

    /// Converts to an `i32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    #[inline]
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
    #[inline]
    pub fn to_u32_saturating(&self) -> Option<u32> {
        self.to_u32_saturating_round(Round::Nearest)
    }

    /// Converts to a `u32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    /// If the value is a NaN, `None` is returned.
    #[inline]
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
    #[inline]
    pub fn to_f32(&self) -> f32 {
        self.to_f32_round(Round::Nearest)
    }

    /// Converts to an `f32`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    #[inline]
    pub fn to_f32_round(&self, round: Round) -> f32 {
        self.to_f64_round(round) as f32
    }

    /// Converts to an `f64`, rounding to the nearest.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    #[inline]
    pub fn to_f64(&self) -> f64 {
        self.to_f64_round(Round::Nearest)
    }

    /// Converts to an `f64`, applying the specified rounding method.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
    #[inline]
    pub fn to_f64_round(&self, round: Round) -> f64 {
        unsafe { mpfr::get_d(self.inner(), rraw(round)) }
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
        let sf = SmallFloat::from(0.0f32);
        assert_eq!(sf.prec(), 24);
        // since we won't change precision, we can mutate the Float
        let mut_sf = unsafe {
            let ptr: *mut Float = &*sf as *const Float as *mut Float;
            &mut *ptr
        };
        let mut exp: c_long = 0;
        let f = unsafe {
            mpfr::set(mut_sf.inner_mut(), self.inner(), rraw(round));
            mpfr::get_d_2exp(&mut exp, mut_sf.inner(), rraw(round))
        };
        assert_eq!(exp as i32 as c_long, exp, "overflow");
        (f as f32, exp as i32)
    }

    /// Converts to an `f64` and an exponent, rounding to the nearest.
    ///
    /// The returned `f64` is in the range 0.5 ≤ *x* < 1.
    ///
    /// If the value is too small or too large for the target type,
    /// the minimum or maximum value allowed is returned.
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
    #[inline]
    pub fn to_f64_exp_round(&self, round: Round) -> (f64, i32) {
        let mut exp: c_long = 0;
        let f =
            unsafe { mpfr::get_d_2exp(&mut exp, self.inner(), rraw(round)) };
        assert_eq!(exp as i32 as c_long, exp, "overflow");
        (f, exp as i32)
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
    /// let neg_inf = Float::with_val(53, Special::MinusInfinity);
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
        make_string(self, radix, num_digits, round, false)
    }

    /// Parses a `Float` from a string, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// let mut f = Float::new(53);
    /// f.assign_str("12.5e2").unwrap();
    /// assert_eq!(f, 12.5e2);
    /// let ret = f.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    #[inline]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseFloatError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Float` from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// let mut f = Float::new(4);
    /// let dir = f.assign_str_round("14.1", Round::Down).unwrap();
    /// assert_eq!(f, 14);
    /// assert_eq!(dir, Ordering::Less);
    /// ```
    #[inline]
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
    /// use rug::Float;
    /// let mut f = Float::new(53);
    /// f.assign_str_radix("f.f", 16).unwrap();
    /// assert_eq!(f, 15.9375);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseFloatError> {
        self.assign_str_radix_round(src, radix, Round::Nearest)?;
        Ok(())
    }

    /// Parses a `Float` from a string with the specified radix,
    /// applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::Round;
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
    #[inline]
    pub fn assign_str_radix_round(
        &mut self,
        src: &str,
        radix: i32,
        round: Round,
    ) -> Result<Ordering, ParseFloatError> {
        Ok(self.assign_round(
            Float::valid_str_radix(src, radix)?,
            round,
        ))
    }

    /// Borrows a negated copy of the `Float`.
    ///
    /// The returned object implements `Deref` with a `Float` target.
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
        unsafe {
            if self.is_nan() {
                mpfr::set_nanflag();
            } else {
                ret.inner.sign.neg_assign();
            }
        }
        ret
    }

    /// Borrows an absolute copy of the `Float`.
    ///
    /// The returned object implements `Deref` with a `Float` target.
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
        unsafe {
            if self.is_nan() {
                mpfr::set_nanflag();
            } else {
                ret.inner.sign = 1;
            }
        }
        ret
    }

    /// Returns `true` if `self` is an integer.
    #[inline]
    pub fn is_integer(&self) -> bool {
        unsafe { mpfr::integer_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is not a number.
    #[inline]
    pub fn is_nan(&self) -> bool {
        unsafe { mpfr::nan_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus infinity.
    #[inline]
    pub fn is_infinite(&self) -> bool {
        unsafe { mpfr::inf_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a finite number,
    /// that is neither NaN nor infinity.
    #[inline]
    pub fn is_finite(&self) -> bool {
        unsafe { mpfr::number_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is plus or minus zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        unsafe { mpfr::zero_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a normal number, that is neither
    /// NaN, nor infinity, nor zero. Note that `Float` cannot be
    /// subnormal.
    #[inline]
    pub fn is_normal(&self) -> bool {
        unsafe { mpfr::regular_p(self.inner()) != 0 }
    }

    /// Returns `Ordering::Less` if `self` is less than zero,
    /// `Ordering::Greater` if `self` is greater than zero, or
    /// `Ordering::Equal` if `self` is equal to zero.
    #[inline]
    pub fn sign(&self) -> Option<Ordering> {
        if self.is_nan() {
            None
        } else {
            let ret = unsafe { mpfr::sgn(self.inner()) };
            Some(ordering1(ret))
        }
    }

    /// Compares the absolute values of `self` and `other`.
    #[inline]
    pub fn cmp_abs(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(ordering1(mpfr::cmpabs(self.inner(), other.inner()))),
                _ => None,
            }
        }
    }

    /// Returns the exponent of `self` if `self` is a normal number,
    /// otherwise `None`. The significand is assumed to be in the
    /// range [0.5,1).
    #[inline]
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
    #[inline]
    pub fn get_sign(&self) -> bool {
        unsafe { mpfr::signbit(self.inner()) != 0 }
    }

    /// Emulate subnormal numbers, rounding to the nearest. This
    /// method has no effect if the value is not in the subnormal
    /// range.
    #[inline]
    pub fn subnormalize(&mut self) -> &mut Float {
        self.subnormalize_round(Ordering::Equal, Round::Nearest);
        self
    }

    /// Emulate subnormal numbers, applying the specified rounding
    /// method. This method simply propagates `prev_rounding` if the
    /// value is not in the subnormal range.
    #[inline]
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
        let ret =
            unsafe { mpfr::subnormalize(self.inner_mut(), prev, rraw(round)) };
        ordering1(ret)
    }

    math_op1_float! {
        mpfr::sqr;
        /// Computes the square, rounding to the nearest.
        fn square();
        /// Computes the square, rounding to the nearest.
        fn square_mut;
        /// Computes the square, applying the specified rounding method.
        fn square_round;
        /// Compuets the square.
        fn square_ref -> SquareRef;
    }
    math_op1_float! {
        mpfr::sqrt;
        /// Computes the square root, rounding to the nearest.
        fn sqrt();
        /// Computes the square root, rounding to the nearest.
        fn sqrt_mut;
        /// Computes the square root, applying the specified rounding
        /// method.
        fn sqrt_round;
        /// Computes the square root.
        fn sqrt_ref -> SqrtRef;
    }

    /// Sets `self` to the square root of `u`, rounding to the
    /// nearest.
    #[inline]
    pub fn assign_sqrt_u(&mut self, u: u32) {
        self.assign_sqrt_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the square root of `u`, applying the specified
    /// rounding method.
    #[inline]
    pub fn assign_sqrt_u_round(&mut self, u: u32, round: Round) -> Ordering {
        let ret =
            unsafe { mpfr::sqrt_ui(self.inner_mut(), u.into(), rraw(round)) };
        ordering1(ret)
    }

    math_op1_float! {
        mpfr::rec_sqrt;
        /// Computes the reciprocal square root, rounding to the nearest.
        fn recip_sqrt();
        /// Computes the reciprocal square root, rounding to the nearest.
        fn recip_sqrt_mut;
        /// Computes the reciprocal square root, applying the specified
        /// rounding method.
        fn recip_sqrt_round;
        /// Computes the reciprocal square root.
        fn recip_sqrt_ref -> RecipSqrtRef;
    }
    math_op1_float! {
        mpfr::cbrt;
        /// Computes the cube root, rounding to the nearest.
        fn cbrt();
        /// Computes the cube root, rounding to the nearest.
        fn cbrt_mut;
        /// Computes the cube root, applying the specified rounding
        /// method.
        fn cbrt_round;
        /// Computes the cube root.
        fn cbrt_ref -> CbrtRef;
    }
    math_op1_float! {
        mpfr::root;
        /// Computes the <i>k</i>th root, rounding to the nearest.
        fn root(k: u32);
        /// Computes the <i>k</i>th root, rounding to the nearest.
        fn root_mut;
        /// Computes the <i>k</i>th root, applying the specified
        /// rounding method.
        fn root_round;
        /// Computes the <i>k</i>th root.
        fn root_ref -> RootRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::abs, rraw;
        /// Computes the absolute value.
        fn abs();
        /// Computes the absolute value.
        fn abs_mut;
        /// Computes the absolute value.
        fn abs_ref -> AbsRef;
    }
    math_op1_float! {
        xmpfr::recip;
        /// Computes the reciprocal, rounding to the nearest.
        fn recip();
        /// Computes the reciprocal, rounding to the nearest.
        fn recip_mut;
        /// Computes the reciprocal, applying the specified rounding
        /// method.
        fn recip_round;
        /// Computes the reciprocal.
        fn recip_ref -> RecipRef;
    }
    math_op2_float! {
        mpfr::dim;
        /// Computes the positive difference between `self` and
        /// `other`, rounding to the nearest.
        fn pos_diff(other);
        /// Computes the positive difference between `self` and
        /// `other`, rounding to the nearest.
        fn pos_diff_mut;
        /// Computes the positive difference between `self` and
        /// `other`, applying the specified rounding method.
        fn pos_diff_round;
        /// Computes the positive difference.
        fn pos_diff_ref -> AbsDiffRef;
    }
    math_op1_float! {
        mpfr::log;
        /// Computes the natural logarithm, rounding to the nearest.
        fn ln();
        /// Computes the natural logarithm, rounding to the nearest.
        fn ln_mut;
        /// Computes the natural logarithm, applying the specified
        /// rounding method.
        fn ln_round;
        /// Computes the natural logarithm.
        fn ln_ref -> LnRef;
    }
    math_op1_float! {
        mpfr::log2;
        /// Computes the logarithm to base 2, rounding to the nearest.
        fn log2();
        /// Computes the logarithm to base 2, rounding to the nearest.
        fn log2_mut;
        /// Computes the logarithm to base 2, applying the specified
        /// rounding method.
        fn log2_round;
        /// Computes the logarithm to base 2.
        fn log2_ref -> Log2Ref;
    }
    math_op1_float! {
        mpfr::log10;
        /// Computes the logarithm to base 10, rounding to the nearest.
        fn log10();
        /// Computes the logarithm to base 10, rounding to the nearest.
        fn log10_mut;
        /// Computes the logarithm to base 10, applying the specified
        /// rounding method.
        fn log10_round;
        /// Computes the logarithm to base 10.
        fn log10_ref -> Log10Ref;
    }
    math_op1_float! {
        mpfr::exp;
        /// Computes the exponential, rounding to the nearest.
        fn exp();
        /// Computes the exponential, rounding to the nearest.
        fn exp_mut;
        /// Computes the exponential, applying the specified rounding
        /// method.
        fn exp_round;
        /// Computes the exponential.
        fn exp_ref -> ExpRef;
    }
    math_op1_float! {
        mpfr::exp2;
        /// Computes 2 to the power of `self`, rounding to the nearest.
        fn exp2();
        /// Computes 2 to the power of `self`, rounding to the nearest.
        fn exp2_mut;
        /// Computes 2 to the power of `self`, applying the specified
        /// rounding method.
        fn exp2_round;
        /// Computes 2 to the power of the value.
        fn exp2_ref -> Exp2Ref;
    }
    math_op1_float! {
        mpfr::exp10;
        /// Computes 10 to the power of `self`, rounding to the nearest.
        fn exp10();
        /// Computes 10 to the power of `self`, rounding to the nearest.
        fn exp10_mut;
        /// Computes 10 to the power of `self`, applying the specified
        /// rounding method.
        fn exp10_round;
        /// Computes 10 to the power of the value.
        fn exp10_ref -> Exp10Ref;
    }
    math_op1_float! {
        mpfr::sin;
        /// Computes the sine, rounding to the nearest.
        fn sin();
        /// Computes the sine, rounding to the nearest.
        fn sin_mut;
        /// Computes the sine, applying the specified rounding method.
        fn sin_round;
        /// Computes the sine.
        fn sin_ref -> SinRef;
    }
    math_op1_float! {
        mpfr::cos;
        /// Computes the cosine, rounding to the nearest.
        fn cos();
        /// Computes the cosine, rounding to the nearest.
        fn cos_mut;
        /// Computes the cosine, applying the specified rounding method.
        fn cos_round;
        /// Computes the cosine.
        fn cos_ref -> CosRef;
    }
    math_op1_float! {
        mpfr::tan;
        /// Computes the tangent, rounding to the nearest.
        fn tan();
        /// Computes the tangent, rounding to the nearest.
        fn tan_mut;
        /// Computes the tangent, applying the specified rounding method.
        fn tan_round;
        /// Computes the tangent.
        fn tan_ref -> TanRef;
    }
    math_op1_2_float! {
        mpfr::sin_cos;
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos(cos);
        /// Computes the sine and cosine of `self`, rounding to the
        /// nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos_mut;
        /// Computes the sine and cosine of `self`, applying the specified
        /// rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sin_cos_round;
        /// Computes the sine and cosine.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Float};
        /// // sin(0.5) = 0.47943, cos(0.5) = 0.87758
        /// let angle = Float::with_val(53, 0.5);
        /// let r = angle.sin_cos_ref();
        /// // use only 10 bits of precision here to
        /// // make comparison easier
        /// let (mut sin, mut cos) = (Float::new(10), Float::new(10));
        /// (&mut sin, &mut cos).assign(r);
        /// assert_eq!(sin, Float::with_val(10, 0.47943));
        /// assert_eq!(cos, Float::with_val(10, 0.87748));
        fn sin_cos_ref -> SinCosRef;
    }
    math_op1_float! {
        mpfr::sec;
        /// Computes the secant, rounding to the nearest.
        fn sec();
        /// Computes the secant, rounding to the nearest.
        fn sec_mut;
        /// Computes the secant, applying the specified rounding method.
        fn sec_round;
        /// Computes the secant.
        fn sec_ref -> SecRef;
    }
    math_op1_float! {
        mpfr::csc;
        /// Computes the cosecant, rounding to the nearest.
        fn csc();
        /// Computes the cosecant, rounding to the nearest.
        fn csc_mut;
        /// Computes the cosecant, applying the specified rounding method.
        fn csc_round;
        /// Computes the cosecant.
        fn csc_ref -> CscRef;
    }
    math_op1_float! {
        mpfr::cot;
        /// Computes the cotangent, rounding to the nearest.
        fn cot();
        /// Computes the cotangent, rounding to the nearest.
        fn cot_mut;
        /// Computes the cotangent, applying the specified rounding
        /// method.
        fn cot_round;
        /// Computes the cotangent.
        fn cot_ref -> CotRef;
    }
    math_op1_float! {
        mpfr::acos;
        /// Computes the arc-cosine, rounding to the nearest.
        fn acos();
        /// Computes the arc-cosine, rounding to the nearest.
        fn acos_mut;
        /// Computes the arc-cosine, applying the specified rounding
        /// method.
        fn acos_round;
        /// Computes the arc-cosine.
        fn acos_ref -> AcosRef;
    }
    math_op1_float! {
        mpfr::asin;
        /// Computes the arc-sine, rounding to the nearest.
        fn asin();
        /// Computes the arc-sine, rounding to the nearest.
        fn asin_mut;
        /// Computes the arc-sine, applying the specified rounding method.
        fn asin_round;
        /// Computes the arc-sine.
        fn asin_ref -> AsinRef;
    }
    math_op1_float! {
        mpfr::atan;
        /// Computes the arc-tangent, rounding to the nearest.
        fn atan();
        /// Computes the arc-tangent, rounding to the nearest.
        fn atan_mut;
        /// Computes the arc-tangent, applying the specified rounding
        /// method.
        fn atan_round;
        /// Computes the arc-tangent.
        fn atan_ref -> AtanRef;
    }
    math_op2_float! {
        mpfr::atan2;
        /// Computes the arc-tangent2 of `self` and `other`, rounding to
        /// the nearest.
        ///
        /// This is similar to the arc-tangent of `self / other`, except
        /// in the cases when either `self` or `other` or both are zero or
        /// infinity.
        fn atan2(other);
        /// Computes the arc-tangent2 of `self` and `other`, rounding to
        /// the nearest.
        ///
        /// This is similar to the arc-tangent of `self / other`, except
        /// in the cases when either `self` or `other` or both are zero or
        /// infinity.
        fn atan2_mut;
        /// Computes the arc-tangent2 of `self` and `other`, applying the
        /// specified rounding method.
        ///
        /// This is similar to the arc-tangent of `self / other`, except
        /// in the cases when either `self` or `other` or both are zero or
        /// infinity.
        fn atan2_round;
        /// Computes the arc-tangent.
        fn atan2_ref -> Atan2Ref;
    }
    math_op1_float! {
        mpfr::sinh;
        /// Computes the hyperbolic sine, rounding to the nearest.
        fn sinh();
        /// Computes the hyperbolic sine, rounding to the nearest.
        fn sinh_mut;
        /// Computes the hyperbolic sine, applying the specified rounding
        /// method.
        fn sinh_round;
        /// Computes the hyperbolic sine.
        fn sinh_ref -> SinhRef;
    }
    math_op1_float! {
        mpfr::cosh;
        /// Computes the hyperbolic cosine, rounding to the nearest.
        fn cosh();
        /// Computes the hyperbolic cosine, rounding to the nearest.
        fn cosh_mut;
        /// Computes the hyperbolic cosine, applying the specified
        /// rounding method.
        fn cosh_round;
        /// Computes the hyperbolic cosine.
        fn cosh_ref -> CoshRef;
    }
    math_op1_float! {
        mpfr::tanh;
        /// Computes the hyperbolic tangent, rounding to the nearest.
        fn tanh();
        /// Computes the hyperbolic tangent, rounding to the nearest.
        fn tanh_mut;
        /// Computes the hyperbolic tangent, applying the specified
        /// rounding method.
        fn tanh_round;
        /// Computes the hyperbolic tangent.
        fn tanh_ref -> TanhRef;
    }
    math_op1_2_float! {
        mpfr::sinh_cosh;
        /// Computes the hyperbolic sine and cosine of `self`,
        /// rounding to the nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sinh_cosh(cos);
        /// Computes the hyperbolic sine and cosine of `self`,
        /// rounding to the nearest.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sinh_cosh_mut;
        /// Computes the hyperbolic sine and cosine of `self`,
        /// applying the specified rounding method.
        ///
        /// The sine is stored in `self` and keeps its precision,
        /// while the cosine is stored in `cos` keeping its precision.
        fn sinh_cosh_round;
        /// Computes the hyperbolic sine and cosine.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Float};
        /// // sinh(0.5) = 0.52110, cosh(0.5) = 1.1276
        /// let angle = Float::with_val(53, 0.5);
        /// let r = angle.sinh_cosh_ref();
        /// // use only 10 bits of precision here to
        /// // make comparison easier
        /// let (mut sinh, mut cosh) = (Float::new(10), Float::new(10));
        /// (&mut sinh, &mut cosh).assign(r);
        /// assert_eq!(sinh, Float::with_val(10, 0.52110));
        /// assert_eq!(cosh, Float::with_val(10, 1.1276));
        fn sinh_cosh_ref -> SinhCoshRef;
    }
    math_op1_float! {
        mpfr::sech;
        /// Computes the hyperbolic secant, rounding to the nearest.
        fn sech();
        /// Computes the hyperbolic secant, rounding to the nearest.
        fn sech_mut;
        /// Computes the hyperbolic secant, applying the specified
        /// rounding method.
        fn sech_round;
        /// Computes the hyperbolic secant.
        fn sech_ref -> SechRef;
    }
    math_op1_float! {
        mpfr::csch;
        /// Computes the hyperbolic cosecant, rounding to the nearest.
        fn csch();
        /// Computes the hyperbolic cosecant, rounding to the nearest.
        fn csch_mut;
        /// Computes the hyperbolic cosecant, applying the specified
        /// rounding method.
        fn csch_round;
        /// Computes the hyperbolic cosecant.
        fn csch_ref -> CschRef;
    }
    math_op1_float! {
        mpfr::coth;
        /// Computes the hyperbolic cotangent, rounding to the nearest.
        fn coth();
        /// Computes the hyperbolic cotangent, rounding to the nearest.
        fn coth_mut;
        /// Computes the hyperbolic cotangent, applying the specified
        /// rounding method.
        fn coth_round;
        /// Computes the hyperbolic cotangent.
        fn coth_ref -> CothRef;
    }
    math_op1_float! {
        mpfr::acosh;
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        fn acosh();
        /// Computes the inverse hyperbolic cosine, rounding to the
        /// nearest.
        fn acosh_mut;
        /// Computes the inverse hyperbolic cosine, applying the specified
        /// rounding method.
        fn acosh_round;
        /// Computes the inverse hyperbolic cosine
        fn acosh_ref -> AcoshRef;
    }
    math_op1_float! {
        mpfr::asinh;
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        fn asinh();
        /// Computes the inverse hyperbolic sine, rounding to the nearest.
        fn asinh_mut;
        /// Computes the inverse hyperbolic sine, applying the specified
        /// rounding method.
        fn asinh_round;
        /// Computes the inverse hyperbolic sine.
        fn asinh_ref -> AsinhRef;
    }
    math_op1_float! {
        mpfr::atanh;
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        fn atanh();
        /// Computes the inverse hyperbolic tangent, rounding to the
        /// nearest.
        fn atanh_mut;
        /// Computes the inverse hyperbolic tangent, applying the
        /// specified rounding method.
        fn atanh_round;
        /// Computes the inverse hyperbolic tangent.
        fn atanh_ref -> AtanhRef;
    }

    /// Sets `self` to the factorial of *u*, rounding to the nearest.
    #[inline]
    pub fn assign_factorial_u(&mut self, u: u32) {
        self.assign_factorial_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the factorial of *u*, applying the specified
    /// rounding method.
    #[inline]
    pub fn assign_factorial_u_round(
        &mut self,
        u: u32,
        round: Round,
    ) -> Ordering {
        let ret =
            unsafe { mpfr::fac_ui(self.inner_mut(), u.into(), rraw(round)) };
        ordering1(ret)
    }

    math_op1_float! {
        mpfr::log1p;
        /// Computes the natural logarithm of one plus `self`, rounding to
        /// the nearest.
        fn ln_1p();
        /// Computes the natural logarithm of one plus `self`, rounding to
        /// the nearest.
        fn ln_1p_mut;
        /// Computes the natural logarithm of one plus `self`, applying
        /// the specified rounding method.
        fn ln_1p_round;
        /// Computes the natural logorithm of one plus the
        /// value.
        fn ln_1p_ref -> Ln1pRef;
    }
    math_op1_float! {
        mpfr::expm1;
        /// Subtracts one from the exponential of `self`, rounding to the
        /// nearest.
        fn exp_m1();
        /// Subtracts one from the exponential of `self`, rounding to the
        /// nearest.
        fn exp_m1_mut;
        /// Subtracts one from the exponential of `self`, applying the
        /// specified rounding method.
        fn exp_m1_round;
        /// Computes one less than the exponential of the
        /// value.
        fn exp_m1_ref -> ExpM1Ref;
    }
    math_op1_float! {
        mpfr::eint;
        /// Computes the exponential integral, rounding to the nearest.
        fn eint();
        /// Computes the exponential integral, rounding to the nearest.
        fn eint_mut;
        /// Computes the exponential integral, applying the specified
        /// rounding method.
        fn eint_round;
        /// Computes the exponential integral.
        fn eint_ref -> EintRef;
    }
    math_op1_float! {
        mpfr::li2;
        /// Computes the real part of the dilogarithm of `self`, rounding
        /// to the nearest.
        fn li2();
        /// Computes the real part of the dilogarithm of `self`, rounding
        /// to the nearest.
        fn li2_mut;
        /// Computes the real part of the dilogarithm of `self`, applying
        /// the specified rounding method.
        fn li2_round;
        /// Computes the real part of the dilogarithm of the
        /// value.
        fn li2_ref -> Li2Ref;
    }
    math_op1_float! {
        mpfr::gamma;
        /// Computes the value of the Gamma function on `self`, rounding
        /// to the nearest.
        fn gamma();
        /// Computes the value of the Gamma function on `self`, rounding
        /// to the nearest.
        fn gamma_mut;
        /// Computes the value of the Gamma function on `self`, applying
        /// the specified rounding method.
        fn gamma_round;
        /// Computes the Gamma function on the value.
        fn gamma_ref -> GammaRef;
    }
    math_op1_float! {
        mpfr::lngamma;
        /// Computes the logarithm of the Gamma function on `self`,
        /// rounding to the nearest.
        fn ln_gamma();
        /// Computes the logarithm of the Gamma function on `self`,
        /// rounding to the nearest.
        fn ln_gamma_mut;
        /// Computes the logarithm of the Gamma function on `self`,
        /// applying the specified rounding method.
        fn ln_gamma_round;
        /// Computes the logarithm of the Gamma function on
        /// the value.
        fn ln_gamma_ref -> LnGammaRef;
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
    /// If the Gamma function is negative, the sign returned is
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
    pub fn ln_abs_gamma(mut self) -> (Float, Ordering) {
        let sign = self.ln_abs_gamma_round(Round::Nearest).0;
        (self, sign)
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
            mpfr::lgamma(self.inner_mut(), sign_ptr, self.inner(), rraw(round))
        };
        let sign_ord = if sign < 0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        (sign_ord, ordering1(ret))
    }

    /// Computes the logarithm of the absolute value of the Gamma
    /// function on `val`.
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
    pub fn ln_abs_gamma_ref(&self) -> LnAbsGammaRef {
        LnAbsGammaRef { ref_self: self }
    }

    math_op1_float! {
        mpfr::digamma;
        /// Computes the value of the Digamma function on `self`, rounding
        /// to the nearest.
        fn digamma();
        /// Computes the value of the Digamma function on `self`, rounding
        /// to the nearest.
        fn digamma_mut;
        /// Computes the value of the Digamma function on `self`, applying
        /// the specified rounding method.
        fn digamma_round;
        /// Computes the Digamma function on the value.
        fn digamma_ref -> DigammaRef;
    }
    math_op1_float! {
        mpfr::zeta;
        /// Computes the value of the Riemann Zeta function on `self`,
        /// rounding to the nearest.
        fn zeta();
        /// Computes the value of the Riemann Zeta function on `self`,
        /// rounding to the nearest.
        fn zeta_mut;
        /// Computes the value of the Riemann Zeta function on `self`,
        /// applying the specified rounding method.
        fn zeta_round;
        /// Computes the Riemann Zeta function on the value.
        fn zeta_ref -> ZetaRef;
    }

    /// Sets `self` to the value of the Riemann Zeta function on *u*,
    /// rounding to the nearest.
    #[inline]
    pub fn assign_zeta_u(&mut self, u: u32) {
        self.assign_zeta_u_round(u, Round::Nearest);
    }

    /// Sets `self` to the value of the Riemann Zeta function on *u*,
    /// applying the specified rounding method.
    #[inline]
    pub fn assign_zeta_u_round(&mut self, u: u32, round: Round) -> Ordering {
        let ret =
            unsafe { mpfr::zeta_ui(self.inner_mut(), u.into(), rraw(round)) };
        ordering1(ret)
    }

    math_op1_float! {
        mpfr::erf;
        /// Computes the value of the error function, rounding to the
        /// nearest.
        fn erf();
        /// Computes the value of the error function, rounding to the
        /// nearest.
        fn erf_mut;
        /// Computes the value of the error function, applying the
        /// specified rounding method.
        fn erf_round;
        /// Computes the error function.
        fn erf_ref -> ErfRef;
    }
    math_op1_float! {
        mpfr::erfc;
        /// Computes the value of the complementary error function,
        /// rounding to the nearest.
        fn erfc();
        /// Computes the value of the complementary error function,
        /// rounding to the nearest.
        fn erfc_mut;
        /// Computes the value of the complementary error function,
        /// applying the specified rounding method.
        fn erfc_round;
        /// Computes the complementary error function.
        fn erfc_ref -> ErfcRef;
    }
    math_op1_float! {
        mpfr::j0;
        /// Computes the value of the first kind Bessel function of
        /// order 0, rounding to the nearest.
        fn j0();
        /// Computes the value of the first kind Bessel function of
        /// order 0, rounding to the nearest.
        fn j0_mut;
        /// Computes the value of the first kind Bessel function of
        /// order 0, applying the specified rounding method.
        fn j0_round;
        /// Computes the first kind Bessel function of order 0.
        fn j0_ref -> J0Ref;
    }
    math_op1_float! {
        mpfr::j1;
        /// Computes the value of the first kind Bessel function of
        /// order 1, rounding to the nearest.
        fn j1();
        /// Computes the value of the first kind Bessel function of
        /// order 1, rounding to the nearest.
        fn j1_mut;
        /// Computes the value of the first kind Bessel function of
        /// order 1, applying the specified rounding method.
        fn j1_round;
        /// Computes the first kind Bessel function of order 1.
        fn j1_ref -> J1Ref;
    }
    math_op1_float! {
        xmpfr::jn;
        /// Computes the value of the first kind Bessel function of
        /// order *n*, rounding to the nearest.
        fn jn(n: i32);
        /// Computes the value of the first kind Bessel function of
        /// order *n*, rounding to the nearest.
        fn jn_mut;
        /// Computes the value of the first kind Bessel function of
        /// order *n*, applying the specified rounding method.
        fn jn_round;
        /// Computes the first kind Bessel function of order *n*.
        fn jn_ref -> JnRef;
    }
    math_op1_float! {
        mpfr::y0;
        /// Computes the value of the second kind Bessel function of
        /// order 0, rounding to the nearest.
        fn y0();
        /// Computes the value of the second kind Bessel function of
        /// order 0, rounding to the nearest.
        fn y0_mut;
        /// Computes the value of the second kind Bessel function of
        /// order 0, applying the specified rounding method.
        fn y0_round;
        /// Computes the second kind Bessel function of order 0.
        fn y0_ref -> Y0Ref;
    }
    math_op1_float! {
        mpfr::y1;
        /// Computes the value of the second kind Bessel function of
        /// order 1, rounding to the nearest.
        fn y1();
        /// Computes the value of the second kind Bessel function of
        /// order 1, rounding to the nearest.
        fn y1_mut;
        /// Computes the value of the second kind Bessel function of
        /// order 1, applying the specified rounding method.
        fn y1_round;
        /// Computes the second kind Bessel function of order 1.
        fn y1_ref -> Y1Ref;
    }
    math_op1_float! {
        xmpfr::yn;
        /// Computes the value of the second kind Bessel function of
        /// order *n*, rounding to the nearest.
        fn yn(n: i32);
        /// Computes the value of the second kind Bessel function of
        /// order *n*, rounding to the nearest.
        fn yn_mut;
        /// Computes the value of the second kind Bessel function of
        /// order *n*, applying the specified rounding method.
        fn yn_round;
        /// Computes the second kind Bessel function of order *n*.
        fn yn_ref -> YnRef;
    }
    math_op2_float! {
        mpfr::agm;
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// rounding to the nearest.
        fn agm(other);
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// rounding to the nearest.
        fn agm_mut;
        /// Computes the arithmetic-geometric mean of `self` and `other`,
        /// applying the specified rounding method.
        fn agm_round;
        /// Computes the arithmetic-geometric mean.
        fn agm_ref -> AgmRef;
    }
    math_op2_float! {
        mpfr::hypot;
        /// Computes the Euclidean norm of `self` and `other`, rounding to
        /// the nearest.
        fn hypot(other);
        /// Computes the Euclidean norm of `self` and `other`, rounding to
        /// the nearest.
        fn hypot_mut;
        /// Computes the Euclidean norm of `self` and `other`, applying
        /// the specified rounding method.
        fn hypot_round;
        /// Computes the Euclidean norm.
        fn hypot_ref -> HypotRef;
    }
    math_op1_float! {
        mpfr::ai;
        /// Computes the value of the Airy function Ai on `self`, rounding
        /// to the nearest.
        fn ai();
        /// Computes the value of the Airy function Ai on `self`, rounding
        /// to the nearest.
        fn ai_mut;
        /// Computes the value of the Airy function Ai on `self`, applying
        /// the specified rounding method.
        fn ai_round;
        /// Computes the Airy function Ai on the value.
        fn ai_ref -> AiRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::rint_ceil, rraw;
        /// Rounds up to the next higher integer.
        fn ceil();
        /// Rounds up to the next higher integer.
        fn ceil_mut;
        /// Rounds up to the next higher integer. The result may be
        /// rounded again when assigned to the target.
        fn ceil_ref -> CeilRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::rint_floor, rraw;
        /// Rounds down to the next lower integer.
        fn floor();
        /// Rounds down to the next lower integer.
        fn floor_mut;
        /// Rounds down to the next lower integer. The result may be
        /// rounded again when assigned to the target.
        fn floor_ref -> FloorRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::rint_round, rraw;
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero.
        fn round();
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero.
        fn round_mut;
        /// Rounds to the nearest integer, rounding half-way cases
        /// away from zero. The result may be rounded again when
        /// assigned to the target.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{AssignRound, Float};
        /// use rug::float::Round;
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
        fn round_ref -> RoundRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::rint_trunc, rraw;
        /// Rounds to the next integer towards zero.
        fn trunc();
        /// Rounds to the next integer towards zero.
        fn trunc_mut;
        /// Rounds to the next integer towards zero. The result may be
        /// rounded again when assigned to the target.
        fn trunc_ref -> TruncRef;
    }
    math_op1_no_round! {
        Float;
        mpfr::frac, rraw;
        /// Gets the fractional part of the number.
        fn fract();
        /// Gets the fractional part of the number.
        fn fract_mut;
        /// Gets the fractional part of the number.
        fn fract_ref -> FractRef;
    }
    math_op1_2_float! {
        mpfr::modf;
        /// Gets the integer and fractional parts of the number,
        /// rounding to the nearest.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        fn trunc_fract(fract);
        /// Gets the integer and fractional parts of the number,
        /// rounding to the nearest.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        fn trunc_fract_mut;
        /// Gets the integer and fractional parts of the number,
        /// applying the specified rounding method.
        ///
        /// The integer part is stored in `self` and keeps its
        /// precision, while the fractional part is stored in `fract`
        /// keeping its precision.
        fn trunc_fract_round;
        /// Gets the integer and fractional parts of the number.
        fn trunc_fract_ref -> TruncFractRef;
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
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut f = Float::new(2);
    /// f.assign_random_bits(&mut rand).unwrap();
    /// assert!(f == 0.0 || f == 0.25 || f == 0.5 || f == 0.75);
    /// println!("0.0 <= {} < 1.0", f);
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
    #[inline]
    pub fn assign_random_bits(
        &mut self,
        rng: &mut RandState,
    ) -> Result<(), ()> {
        let err = unsafe { mpfr::urandomb(self.inner_mut(), rng.inner_mut()) };
        if err != 0 {
            Err(())
        } else {
            Ok(())
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the continuous range 0 ≤ *x* < 1,
    /// and rounds to the nearest.
    ///
    /// The result can be rounded up to be eual to one. This is
    /// equivalent to calling
    /// [`assign_random_cont_round(rng, Round::Nearest)`]
    /// (#method.assign_random_cont_round).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut f = Float::new(2);
    /// f.assign_random_cont(&mut rand);
    /// // The significand is either 0b10 or 0b11
    /// //           10          11
    /// assert!(f == 1.0 || f == 0.75 ||
    ///         f == 0.5 || f == 0.375 ||
    ///         f == 0.25 || f <= 0.1875);
    /// ```
    #[inline]
    pub fn assign_random_cont(&mut self, rng: &mut RandState) {
        self.assign_random_cont_round(rng, Round::Nearest);
    }

    #[cfg(feature = "rand")]
    /// Generates a random number in the continous range 0 ≤ *x* < 1,
    /// and applies the specified rounding method.
    ///
    /// The result can be rounded up to be equal to one. Unlike the
    /// [`assign_random_bits`](#method.assign_random_bits) method
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
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::rand::RandState;
    /// use std::cmp::Ordering;
    /// let mut rand = RandState::new();
    /// let mut f = Float::new(2);
    /// let dir = f.assign_random_cont_round(&mut rand, Round::Down);
    /// // We cannot have an exact value without rounding.
    /// assert_eq!(dir, Ordering::Less);
    /// // The significand is either 0b11 or 0b10
    /// //           11           10
    /// assert!(f == 0.75 || f == 0.5 ||
    ///         f == 0.375 || f == 0.25 ||
    ///         f <= 0.1875);
    /// ```
    #[inline]
    pub fn assign_random_cont_round(
        &mut self,
        rng: &mut RandState,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::urandom(self.inner_mut(), rng.inner_mut(), rraw(round))
        };
        ordering1(ret)
    }

    #[cfg(feature = "rand")]
    /// Generates two random numbers according to a standard normal
    /// Gaussian distribution, rounding to the nearest.
    ///
    /// If `other` is `None`, only one value is generated.
    #[inline]
    pub fn assign_random_gaussian(
        &mut self,
        other: Option<&mut Float>,
        rng: &mut RandState,
    ) {
        self.assign_random_gaussian_round(other, rng, Default::default());
    }

    #[cfg(feature = "rand")]
    /// Generates two random numbers according to a standard normal
    /// Gaussian distribution, applying the specified rounding method.
    ///
    /// If `other` is `None`, only one value is generated.
    #[inline]
    pub fn assign_random_gaussian_round(
        &mut self,
        other: Option<&mut Float>,
        rng: &mut RandState,
        round: Round,
    ) -> (Ordering, Ordering) {
        let second_ptr = match other {
            Some(r) => unsafe { r.inner_mut() },
            None => ptr::null_mut(),
        };
        let ret = unsafe {
            mpfr::grandom(
                self.inner_mut(),
                second_ptr,
                rng.inner_mut(),
                rraw(round),
            )
        };
        ordering2(ret)
    }
}

impl Display for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

impl<T> Assign<T> for Float
where
    Float: AssignRound<T, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, other: T) {
        self.assign_round(other, Round::Nearest);
    }
}

impl AssignRound<Constant> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, other: Constant, round: Round) -> Ordering {
        let ret = unsafe {
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
        ordering1(ret)
    }
}

impl AssignRound<Special> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, other: Special, _round: Round) -> Ordering {
        unsafe {
            const EXP_MAX: c_long = ((!0 as c_ulong) >> 1) as c_long;
            const EXP_ZERO: c_long = 0 - EXP_MAX;
            const EXP_INF: c_long = 2 - EXP_MAX;
            match other {
                Special::Zero => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::MinusZero => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::Infinity => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_INF;
                }
                Special::MinusInfinity => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_INF;
                }
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
            #[inline]
            fn assign_round(
                &mut self,
                other: &'a $T,
                round: Round
            ) -> Ordering {
                let ret = unsafe {
                    $func(self.inner_mut(), other.inner(), rraw(round))
                };
                ordering1(ret)
            }
        }

        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, other: $T, round: Round) -> Ordering {
                self.assign_round(&other, round)
            }
        }
    };
}

assign! { Float, mpfr::set }
#[cfg(feature = "integer")]
assign! { Integer, mpfr::set_z }
#[cfg(feature = "rational")]
assign! { Rational, mpfr::set_q }

ref_math_op1_float! { mpfr::sqr; struct SquareRef {} }
ref_math_op1_float! { mpfr::sqrt; struct SqrtRef {} }
ref_math_op1_float! { mpfr::rec_sqrt; struct RecipSqrtRef {} }
ref_math_op1_float! { mpfr::cbrt; struct CbrtRef {} }
ref_math_op1_float! { mpfr::root; struct RootRef { k: u32 } }
ref_math_op1_float! { mpfr::abs; struct AbsRef {} }
ref_math_op1_float! { xmpfr::recip; struct RecipRef {} }
ref_math_op2_float! { mpfr::dim; struct AbsDiffRef { other } }
ref_math_op1_float! { mpfr::log; struct LnRef {} }
ref_math_op1_float! { mpfr::log2; struct Log2Ref {} }
ref_math_op1_float! { mpfr::log10; struct Log10Ref {} }
ref_math_op1_float! { mpfr::exp; struct ExpRef {} }
ref_math_op1_float! { mpfr::exp2; struct Exp2Ref {} }
ref_math_op1_float! { mpfr::exp10; struct Exp10Ref {} }
ref_math_op1_float! { mpfr::sin; struct SinRef {} }
ref_math_op1_float! { mpfr::cos; struct CosRef {} }
ref_math_op1_float! { mpfr::tan; struct TanRef {} }
ref_math_op1_2_float! { mpfr::sin_cos; struct SinCosRef {} }
ref_math_op1_float! { mpfr::sec; struct SecRef {} }
ref_math_op1_float! { mpfr::csc; struct CscRef {} }
ref_math_op1_float! { mpfr::cot; struct CotRef {} }
ref_math_op1_float! { mpfr::acos; struct AcosRef {} }
ref_math_op1_float! { mpfr::asin; struct AsinRef {} }
ref_math_op1_float! { mpfr::atan; struct AtanRef {} }
ref_math_op2_float! { mpfr::atan2; struct Atan2Ref { other } }
ref_math_op1_float! { mpfr::cosh; struct CoshRef {} }
ref_math_op1_float! { mpfr::sinh; struct SinhRef {} }
ref_math_op1_float! { mpfr::tanh; struct TanhRef {} }
ref_math_op1_2_float! { mpfr::sinh_cosh; struct SinhCoshRef {} }
ref_math_op1_float! { mpfr::sech; struct SechRef {} }
ref_math_op1_float! { mpfr::csch; struct CschRef {} }
ref_math_op1_float! { mpfr::coth; struct CothRef {} }
ref_math_op1_float! { mpfr::acosh; struct AcoshRef {} }
ref_math_op1_float! { mpfr::asinh; struct AsinhRef {} }
ref_math_op1_float! { mpfr::atanh; struct AtanhRef {} }
ref_math_op1_float! { mpfr::log1p; struct Ln1pRef {} }
ref_math_op1_float! { mpfr::expm1; struct ExpM1Ref {} }
ref_math_op1_float! { mpfr::eint; struct EintRef {} }
ref_math_op1_float! { mpfr::li2; struct Li2Ref {} }
ref_math_op1_float! { mpfr::gamma; struct GammaRef {} }
ref_math_op1_float! { mpfr::lngamma; struct LnGammaRef {} }

pub struct LnAbsGammaRef<'a> {
    ref_self: &'a Float,
}

impl<'a> Assign<LnAbsGammaRef<'a>> for (&'a mut Float, &'a mut Ordering) {
    #[inline]
    fn assign(&mut self, src: LnAbsGammaRef<'a>) {
        self.assign_round(src, Round::Nearest);
    }
}

impl<'a> AssignRound<LnAbsGammaRef<'a>> for (&'a mut Float, &'a mut Ordering) {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: LnAbsGammaRef<'a>,
        round: Round,
    ) -> Ordering {
        let mut sign: c_int = 0;
        let sign_ptr = &mut sign as *mut c_int;
        let ret = unsafe {
            mpfr::lgamma(
                self.0.inner_mut(),
                sign_ptr,
                src.ref_self.inner(),
                rraw(round),
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

ref_math_op1_float! { mpfr::digamma; struct DigammaRef {} }
ref_math_op1_float! { mpfr::zeta; struct ZetaRef {} }
ref_math_op1_float! { mpfr::erf; struct ErfRef {} }
ref_math_op1_float! { mpfr::erfc; struct ErfcRef {} }
ref_math_op1_float! { mpfr::j0; struct J0Ref {} }
ref_math_op1_float! { mpfr::j1; struct J1Ref {} }
ref_math_op1_float! { xmpfr::jn; struct JnRef { n: i32 } }
ref_math_op1_float! { mpfr::y0; struct Y0Ref {} }
ref_math_op1_float! { mpfr::y1; struct Y1Ref {} }
ref_math_op1_float! { xmpfr::yn; struct YnRef { n: i32 } }
ref_math_op2_float! { mpfr::agm; struct AgmRef { other } }
ref_math_op2_float! { mpfr::hypot; struct HypotRef { other } }
ref_math_op1_float! { mpfr::ai; struct AiRef {} }
ref_math_op1_float! { mpfr::rint_ceil; struct CeilRef {} }
ref_math_op1_float! { mpfr::rint_floor; struct FloorRef {} }
ref_math_op1_float! { mpfr::rint_round; struct RoundRef {} }
ref_math_op1_float! { mpfr::rint_trunc; struct TruncRef {} }
ref_math_op1_float! { mpfr::frac; struct FractRef {} }
ref_math_op1_2_float! { mpfr::modf; struct TruncFractRef {} }

#[derive(Clone, Copy)]
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

impl Neg for Float {
    type Output = Float;
    #[inline]
    fn neg(mut self) -> Float {
        self.neg_assign();
        self
    }
}

impl NegAssign for Float {
    #[inline]
    fn neg_assign(&mut self) {
        unsafe {
            mpfr::neg(self.inner_mut(), self.inner(), rraw(Round::Nearest));
        }
    }
}

impl<'a> Neg for &'a Float {
    type Output = NegRef<'a>;
    #[inline]
    fn neg(self) -> NegRef<'a> {
        NegRef { val: self }
    }
}

pub struct NegRef<'a> {
    val: &'a Float,
}

impl<'a> AssignRound<NegRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NegRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::neg(self.inner_mut(), src.val.inner(), rraw(round))
        };
        ordering1(ret)
    }
}

macro_rules! arith_binary_self_float {
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
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Ref
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_forward_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident $RefOwn:ident
    } => {
        arith_forward_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $RefOwn
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_commut_float {
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
            Float, Round => Ordering;
            $func, rraw => ordering1;
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

#[cfg(feature = "integer")]
macro_rules! arith_noncommut_float {
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
            Float, Round => Ordering;
            $func, $func_from, rraw => ordering1;
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

arith_binary_self_float! {
    mpfr::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddRef
}
arith_binary_self_float! {
    mpfr::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubRef
}
arith_binary_self_float! {
    mpfr::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulRef
}
arith_binary_self_float! {
    mpfr::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivRef
}
arith_binary_self_float! {
    mpfr::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowRef
}

#[cfg(feature = "integer")]
arith_commut_float! {
    mpfr::add_z;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Integer;
    AddRefInteger AddRefIntegerOwn
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::sub_z, mpfr::z_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Integer;
    SubRefInteger SubFromRefInteger SubRefIntegerOwn SubFromRefIntegerOwn
}
#[cfg(feature = "integer")]
arith_commut_float! {
    mpfr::mul_z;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Integer;
    MulRefInteger MulRefIntegerOwn
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::div_z, xmpfr::z_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Integer;
    DivRefInteger DivFromRefInteger DivRefIntegerOwn DivFromRefIntegerOwn
}
#[cfg(feature = "integer")]
arith_forward_float! {
    mpfr::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowRefInteger PowRefIntegerOwn
}

#[cfg(feature = "rational")]
arith_commut_float! {
    mpfr::add_q;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Rational;
    AddRefRational AddRefRationalOwn
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::sub_q, xmpfr::q_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Rational;
    SubRefRational SubFromRefRational SubRefRationalOwn SubFromRefRationalOwn
}
#[cfg(feature = "rational")]
arith_commut_float! {
    mpfr::mul_q;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Rational;
    MulRefRational MulRefRationalOwn
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::div_q, xmpfr::q_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Rational;
    DivRefRational DivFromRefRational DivRefRationalOwn DivFromRefRationalOwn
}

macro_rules! arith_prim_exact_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_exact_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_commut_float {
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
            Float, Round => Ordering;
            $func, rraw => ordering1;
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

macro_rules! arith_prim_noncommut_float {
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
            Float, Round => Ordering;
            $func, $func_from, rraw => ordering1;
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

macro_rules! conv_ops {
    {
        ($T:ty, $set:path),
        ($AddRef:ident $add:path,
         $SubRef:ident $sub:path,
         $SubFromRef:ident $sub_from:path),
        ($MulRef:ident $mul:path,
         $DivRef:ident $div: path,
         $DivFromRef:ident $div_from:path)
    } => {
        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, val: $T, round: Round) -> Ordering {
                let ret = unsafe {
                    $set(self.inner_mut(), val.into(), rraw(round))
                };
                ordering1(ret)
            }
        }

        arith_prim_commut_float! {
            $add;
            Add add;
            AddAssign add_assign;
            AddAssignRound add_assign_round;
            AddFrom add_from;
            AddFromRound add_from_round;
            $T;
            $AddRef
        }
        arith_prim_noncommut_float! {
            $sub, $sub_from;
            Sub sub;
            SubAssign sub_assign;
            SubAssignRound sub_assign_round;
            SubFrom sub_from;
            SubFromRound sub_from_round;
            $T;
            $SubRef $SubFromRef
        }
        arith_prim_commut_float! {
            $mul;
            Mul mul;
            MulAssign mul_assign;
            MulAssignRound mul_assign_round;
            MulFrom mul_from;
            MulFromRound mul_from_round;
            $T;
            $MulRef
        }
        arith_prim_noncommut_float! {
            $div, $div_from;
            Div div;
            DivAssign div_assign;
            DivAssignRound div_assign_round;
            DivFrom div_from;
            DivFromRound div_from_round;
            $T;
            $DivRef $DivFromRef
        }
    }
}

conv_ops! {
    (i32, mpfr::set_si),
    (AddRefI32 mpfr::add_si,
     SubRefI32 mpfr::sub_si,
     SubFromRefI32 mpfr::si_sub),
    (MulRefI32 mpfr::mul_si,
     DivRefI32 mpfr::div_si,
     DivFromRefI32 mpfr::si_div)
}

impl AssignRound<i64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, other: i64, round: Round) -> Ordering {
        let ret =
            unsafe { xmpfr::set_i64(self.inner_mut(), other, rraw(round)) };
        ordering1(ret)
    }
}

conv_ops! {
    (u32, mpfr::set_ui),
    (AddRefU32 mpfr::add_ui,
     SubRefU32 mpfr::sub_ui,
     SubFromRefU32 mpfr::ui_sub),
    (MulRefU32 mpfr::mul_ui,
     DivRefU32 mpfr::div_ui,
     DivFromRefU32 mpfr::ui_div)
}

impl AssignRound<u64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, other: u64, round: Round) -> Ordering {
        let ret =
            unsafe { xmpfr::set_u64(self.inner_mut(), other, rraw(round)) };
        ordering1(ret)
    }
}

conv_ops! {
    (f32, xmpfr::set_f32),
    (AddRefF32 xmpfr::add_f32,
     SubRefF32 xmpfr::sub_f32,
     SubFromRefF32 xmpfr::f32_sub),
    (MulRefF32 xmpfr::mul_f32,
     DivRefF32 xmpfr::div_f32,
     DivFromRefF32 xmpfr::f32_div)
}
conv_ops! {
    (f64, mpfr::set_d),
    (AddRefF64 mpfr::add_d,
     SubRefF64 mpfr::sub_d,
     SubFromRefF64 mpfr::d_sub),
    (MulRefF64 mpfr::mul_d,
     DivRefF64 mpfr::div_d,
     DivFromRefF64 mpfr::d_div)
}

arith_prim_exact_float! {
    mpfr::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlRefU32
}
arith_prim_exact_float! {
    mpfr::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrRefU32
}
arith_prim_noncommut_float!{
    mpfr::pow_ui, mpfr::ui_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    u32;
    PowRefU32 PowFromRefU32
}
arith_prim_exact_float! {
    mpfr::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlRefI32
}
arith_prim_exact_float! {
    mpfr::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrRefI32
}
arith_prim_noncommut_float!{
    mpfr::pow_si, xmpfr::si_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    i32;
    PowRefI32 PowFromRefI32
}
arith_prim_noncommut_float!{
    xmpfr::pow_f64, xmpfr::f64_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f64;
    PowRefF64 PowFromRefF64
}
arith_prim_noncommut_float!{
    xmpfr::pow_f32, xmpfr::f32_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f32;
    PowRefF32 PowFromRefF32
}

macro_rules! mul_op_round {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        // x # mul
        impl<'a> $Imp<MulRef<'a>> for Float {
            type Output = Float;
            #[inline]
            fn $method(mut self, rhs: MulRef) -> Float {
                self.$method_assign(rhs);
                self
            }
        }

        // x #= mul
        impl<'a> $ImpAssign<MulRef<'a>> for Float {
            #[inline]
            fn $method_assign(&mut self, rhs: MulRef) {
                self.$method_assign_round(rhs, Default::default());
            }
        }

        // x #= mul with rounding
        impl<'a> $ImpAssignRound<MulRef<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn $method_assign_round(
                &mut self,
                rhs: MulRef,
                round: Round,
            ) -> Ordering {
                let ret = unsafe {
                    $func(self.inner_mut(), self.inner(), rhs, rraw(round))
                };
                ordering1(ret)
            }
        }

        // &x # mul
        impl<'a> $Imp<MulRef<'a>> for &'a Float {
            type Output = $Ref<'a>;
            #[inline]
            fn $method(self, rhs: MulRef<'a>) -> $Ref<'a> {
                $Ref {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            lhs: &'a Float,
            rhs: MulRef<'a>,
        }

        impl<'a> AssignRound<$Ref<'a>> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $Ref, round: Round) -> Ordering {
                let ret = unsafe {
                    $func(
                        self.inner_mut(),
                        src.lhs.inner(),
                        src.rhs,
                        rraw(round),
                    )
                };
                ordering1(ret)
            }
        }
    }
}

mul_op_round! {
    add_mul;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    MulRef;
    AddMulRef
}

mul_op_round! {
    sub_mul;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    MulRef;
    SubMulRef
}

unsafe fn add_mul<'a>(
    rop: *mut mpfr_t,
    acc: *const mpfr_t,
    mul: MulRef<'a>,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::fma(rop, mul.lhs.inner(), mul.rhs.inner(), acc, rnd)
}

unsafe fn sub_mul<'a>(
    rop: *mut mpfr_t,
    acc: *const mpfr_t,
    mul: MulRef<'a>,
    rnd: mpfr::rnd_t,
) -> c_int {
    xmpfr::submul(rop, acc, mul.lhs.inner(), mul.rhs.inner(), rnd)
}

impl PartialEq for Float {
    #[inline]
    fn eq(&self, other: &Float) -> bool {
        unsafe { mpfr::equal_p(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Float {
    /// Returns the ordering of `self` and `other`,
    /// or `None` if one (or both) of them is a NaN.
    #[inline]
    fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(ordering1(mpfr::cmp(self.inner(), other.inner()))),
                _ => None,
            }
        }
    }

    #[inline]
    fn lt(&self, other: &Float) -> bool {
        unsafe { mpfr::less_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn le(&self, other: &Float) -> bool {
        unsafe { mpfr::lessequal_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn gt(&self, other: &Float) -> bool {
        unsafe { mpfr::greater_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn ge(&self, other: &Float) -> bool {
        unsafe { mpfr::greaterequal_p(self.inner(), other.inner()) != 0 }
    }
}

macro_rules! cmp {
    { $T:ty, $eval:expr } => {
        impl PartialEq<$T> for Float {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Float {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                if self.is_nan() {
                    return None;
                }
                Some(ordering1($eval(self.inner(), other)))
            }
        }

        impl PartialEq<Float> for $T {
            #[inline]
            fn eq(&self, other: &Float) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<Float> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    }
}

#[cfg(feature = "integer")]
cmp! { Integer, |f, t: &Integer| unsafe { mpfr::cmp_z(f, t.inner()) } }
#[cfg(feature = "rational")]
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
    let exp = exp.checked_sub(1).expect("overflow");
    if exp != 0 {
        buf.push(if radix <= 10 {
            char_to_upper_if('e', to_upper)
        } else {
            '@'
        });
        let _ = write!(buf, "{}", exp);
    }
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

/// A validated string that can always be converted to a `Float`.
///
/// See the [`Float::valid_str_radix`][valid] method.
///
/// [valid]: ../struct.Float.html#method.valid_str_radix
#[derive(Clone, Debug)]
pub struct ValidFloat<'a> {
    poss: ValidPoss<'a>,
    radix: i32,
    exp_plus: Option<usize>,
}

#[derive(Clone, Debug)]
enum ValidPoss<'a> {
    Bytes(&'a [u8]),
    Special(Special),
}

impl<'a> AssignRound<ValidFloat<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, rhs: ValidFloat, round: Round) -> Ordering {
        let bytes = match rhs.poss {
            ValidPoss::Special(s) => {
                self.assign(s);
                return Ordering::Equal;
            }
            ValidPoss::Bytes(b) => b,
        };
        let mut v = Vec::<u8>::with_capacity(bytes.len() + 1);
        if let Some(exp_plus) = rhs.exp_plus {
            v.extend_from_slice(&bytes[0..exp_plus]);
            v.extend_from_slice(&bytes[exp_plus + 1..]);
        } else {
            v.extend_from_slice(bytes);
        }
        v.push(0);
        let mut c_str_end: *const c_char = ptr::null();
        let ret = unsafe {
            let c_str = CStr::from_bytes_with_nul_unchecked(&v);
            mpfr::strtofr(
                self.inner_mut(),
                c_str.as_ptr(),
                &mut c_str_end as *mut _ as *mut *mut c_char,
                rhs.radix as c_int,
                rraw(round),
            )
        };
        let nul = v.last().unwrap() as *const _ as *const c_char;
        assert_eq!(c_str_end, nul);
        ordering1(ret)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing a `Float`.
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

impl Display for ParseFloatError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Float {}
unsafe impl Sync for Float {}

fn lcase_in(a: &[u8], bs: &[&[u8]]) -> bool {
    'next_b: for b in bs {
        if a.len() != b.len() {
            continue 'next_b;
        }
        for (ac, &bc) in a.iter().map(lcase_ascii).zip(b.iter()) {
            if ac != bc {
                continue 'next_b;
            }
        }
        return true;
    }
    false
}

fn lcase_ascii(byte: &u8) -> u8 {
    if b'A' <= *byte && *byte <= b'Z' {
        *byte - b'A' + b'a'
    } else {
        *byte
    }
}

fn char_to_upper_if(c: char, to_upper: bool) -> char {
    if to_upper {
        c.to_ascii_uppercase()
    } else {
        c
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
