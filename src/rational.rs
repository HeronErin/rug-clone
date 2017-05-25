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

use gmp_mpfr_sys::gmp;
use rugint::{Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign,
             SubFromAssign};
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CString;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
use std::str::FromStr;

/// An arbitrary-precision rational number.
///
/// A rational number is made up of a numerator `Integer` and
/// denominator `Integer`. After rational number functions, the number
/// is always in canonical form, that is, the denominator is always
/// greater than zero, and there are no common factors. Zero is stored
/// as 0/1.
///
/// # Examples
///
/// ```rust
/// extern crate rugint;
/// extern crate rugrat;
///
/// use rugint::Integer;
/// use rugrat::Rational;
///
/// fn main() {
///     let r = Rational::from((-12, 15));
///     let (num, den) = r.into_numer_denom();
///     assert!(num == -4);
///     assert!(den == 5);
///     let one = Rational::from((num, Integer::from(-4)));
///     assert!(one == 1);
/// }
/// ```
pub struct Rational {
    inner: gmp::mpq_t,
}

impl Drop for Rational {
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(&mut self.inner);
        }
    }
}

impl Default for Rational {
    fn default() -> Rational {
        Rational::new()
    }
}

impl Clone for Rational {
    fn clone(&self) -> Rational {
        let mut ret = Rational::new();
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Rational) {
        self.assign(source);
    }
}

impl Rational {
    /// Constructs a new arbitrary-precision rational number with value 0.
    pub fn new() -> Rational {
        let mut inner: gmp::mpq_t = unsafe { mem::uninitialized() };
        unsafe {
            gmp::mpq_init(&mut inner);
        }
        Rational { inner: inner }
    }

    /// Assigns from an `f64` if it is finite, losing no precision.
    fn assign_f64(&mut self, val: f64) -> Result<(), ()> {
        if val.is_finite() {
            unsafe {
                gmp::mpq_set_d(&mut self.inner, val);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    /// Creates a `Rational` from an `f64` if it is finite, losing no
    /// precision.
    pub fn from_f64(val: f64) -> Option<Rational> {
        if val.is_finite() {
            let mut r = Rational::new();
            r.assign_f64(val).unwrap();
            Some(r)
        } else {
            None
        }
    }

    /// Converts `self` to an `f64`, rounding towards zero.
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(&self.inner) }
    }

    /// Assigns from an `f32` if it is finite, losing no precision.
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val as f64)
    }

    /// Creates a `Rational` from an `f32` if it is finite, losing no
    /// precision.
    pub fn from_f32(val: f32) -> Option<Rational> {
        Rational::from_f64(val as f64)
    }

    /// Converts `self` to an `f32`, rounding towards zero.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Borrows the numerator.
    pub fn numer(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_numref(&self.inner as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the denominator.
    pub fn denom(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_denref(&self.inner as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the numerator and denominator.
    pub fn as_numer_denom(&self) -> (&Integer, &Integer) {
        (self.numer(), self.denom())
    }

    /// Borrows the numerator and denominator mutably. The number is
    /// canonicalized when the borrow ends. The denominator must not
    /// be zero when the borrow ends.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // change r from 3/5 to 4/8, which is equal to 1/2
    ///     *num_den.0 += 1;
    ///     *num_den.1 += 3;
    ///     // borrow ends here
    /// }
    /// let num_den = r.as_numer_denom();
    /// assert!(*num_den.0 == 1 && *num_den.1 == 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the borrow ends.
    pub fn as_mut_numer_denom(&mut self) -> MutNumerDenom {
        unsafe {
            let numer_ptr = gmp::mpq_numref(&mut self.inner);
            let denom_ptr = gmp::mpq_denref(&mut self.inner);
            MutNumerDenom(&mut *(numer_ptr as *mut Integer),
                          &mut *(denom_ptr as *mut Integer))
        }
    }

    /// Converts `self` into numerator and denominator integers,
    /// consuming `self`.
    pub fn into_numer_denom(mut self) -> (Integer, Integer) {
        let (mut numer, mut denom) = unsafe { mem::uninitialized() };
        {
            let self_numer_denom = self.as_mut_numer_denom();
            mem::swap(&mut numer, self_numer_denom.0);
            mem::swap(&mut denom, self_numer_denom.1);
            // do not canonicalize uninitialized values
            mem::forget(self_numer_denom);
        }
        mem::forget(self);
        (numer, denom)
    }

    /// Computes the absolute value of `self`
    pub fn abs(&mut self) -> &mut Rational {
        unsafe {
            gmp::mpq_abs(&mut self.inner, &self.inner);
        }
        self
    }

    /// Sets `self` to the absolute value of `val`
    pub fn setabs(&mut self, val: &Rational) -> &mut Rational {
        unsafe {
            gmp::mpq_abs(&mut self.inner, &val.inner);
        }
        self
    }

    /// Computes the reciprocal of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the value is zero.
    pub fn recip(&mut self) -> &mut Rational {
        assert_ne!(self.sign(), Ordering::Equal, "division by zero");
        unsafe {
            gmp::mpq_inv(&mut self.inner, &self.inner);
        }
        self
    }

    /// Sets `self` to the reciprocal of `val`.
    ///
    /// # Panics
    ///
    /// Panics if the value is zero.
    pub fn set_recip(&mut self, val: &Rational) -> &mut Rational {
        assert_ne!(val.sign(), Ordering::Equal, "division by zero");
        unsafe {
            gmp::mpq_inv(&mut self.inner, &val.inner);
        }
        self
    }

    /// Returns `Less` if `self` is less than zero,
    /// `Greater` if `self` is greater than zero,
    /// or `Equal` if `self` is equal to zero.
    pub fn sign(&self) -> Ordering {
        self.numer().sign()
    }

    /// Returns a string representation of `self` for the specified
    /// `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let r1 = Rational::from(0);
    /// assert!(r1.to_string_radix(10) == "0");
    /// let r2 = Rational::from((15, 5));
    /// assert!(r2.to_string_radix(10) == "3");
    /// let r3 = Rational::from((10, -6));
    /// assert!(r3.to_string_radix(10) == "-5/3");
    /// assert!(r3.to_string_radix(5) == "-10/3");
    /// ```
    ///
    /// #Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self, radix: i32) -> String {
        make_string(self, radix, false)
    }

    /// Parses a `Rational` number.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str,
                          radix: i32)
                          -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str_radix(src, radix)?;
        Ok(r)
    }

    /// Parses a `Rational` number from a string.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_str("1/0");
    /// assert!(ret.is_err());
    /// r.assign_str("-24/2").unwrap();
    /// assert!(*r.numer() == -12);
    /// assert!(*r.denom() == 1);
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseRationalError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Rational` number from a string with the specified
    /// radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// r.assign_str_radix("ff/a", 16).unwrap();
    /// assert!(r == (255, 10));
    /// r.assign_str_radix("+ff0/a0", 16).unwrap();
    /// assert!(r == (255, 10));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ParseRationalError> {
        let s = check_str_radix(src, radix)?;
        let c_str = CString::new(s).unwrap();
        let err = unsafe {
            gmp::mpq_set_str(&mut self.inner, c_str.as_ptr(), radix.into())
        };
        assert_eq!(err, 0);
        unsafe {
            gmp::mpq_canonicalize(&mut self.inner);
        }
        Ok(())
    }

    /// Checks if a `Rational` number can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Rational` number. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(src: &str,
                           radix: i32)
                           -> Result<(), ParseRationalError> {
        check_str_radix(src, radix).map(|_| ())
    }
}

fn check_str_radix(src: &str, radix: i32) -> Result<&str, ParseRationalError> {
    use self::ParseRationalError as Error;
    use self::ParseErrorKind as Kind;

    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let (skip_plus, chars) = if src.starts_with('+') {
        (&src[1..], src[1..].chars())
    } else if src.starts_with('-') {
        (src, src[1..].chars())
    } else {
        (src, src.chars())
    };
    let mut got_digit = false;
    let mut denom = false;
    let mut denom_non_zero = false;
    for c in chars {
        if c == '/' {
            if denom {
                return Err(Error { kind: Kind::TooManySlashes });
            }
            if !got_digit {
                return Err(Error { kind: Kind::NumerNoDigits });
            }
            got_digit = false;
            denom = true;
            continue;
        }
        let digit_value = match c {
            '0'...'9' => c as i32 - '0' as i32,
            'a'...'z' => c as i32 - 'a' as i32 + 10,
            'A'...'Z' => c as i32 - 'A' as i32 + 10,
            _ => Err(Error { kind: Kind::InvalidDigit })?,
        };
        if digit_value >= radix {
            return Err(Error { kind: Kind::InvalidDigit });
        }
        got_digit = true;
        if denom && digit_value > 0 {
            denom_non_zero = true;
        }
    }
    if !got_digit && denom {
        return Err(Error { kind: Kind::DenomNoDigits });
    } else if !got_digit {
        return Err(Error { kind: Kind::NoDigits });
    }
    if denom && !denom_non_zero {
        return Err(Error { kind: Kind::DenomZero });
    }
    Ok(skip_plus)
}

impl FromStr for Rational {
    type Err = ParseRationalError;

    /// Parses a `Rational` number.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    fn from_str(src: &str) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str(src)?;
        Ok(r)
    }
}

macro_rules! from_borrow {
    { $d:expr, $T:ty } => {
        impl<'a> From<$T> for Rational {
            /// Constructs a `Rational` number from
            #[doc=$d]
            fn from(t: $T) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

macro_rules! from {
    { $d:expr, $T:ty } => {
        impl From<$T> for Rational {
            /// Constructs a `Rational` number from
            #[doc=$d]
            fn from(t: $T) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

from_borrow! { "another `Rational` number.", &'a Rational }

impl From<Integer> for Rational {
    /// Constructs a `Rational` number from an `Integer`.
    ///
    /// This constructor allocates one new `Integer` and reuses the
    /// allocation for `val`.
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_borrow! { "an `Integer`.", &'a Integer }

impl From<(Integer, Integer)> for Rational {
    /// Constructs a `Rational` number from a numerator `Integer` and
    /// denominator `Integer`.
    ///
    /// This constructor does not allocate, as it reuses the `Integer`
    /// components.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn from((mut num, mut den): (Integer, Integer)) -> Rational {
        assert_ne!(den.sign(), Ordering::Equal, "division by zero");
        let mut dst: Rational = unsafe { mem::uninitialized() };
        {
            let num_den = dst.as_mut_numer_denom();
            mem::swap(&mut num, num_den.0);
            mem::swap(&mut den, num_den.1);
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

from_borrow! { "a numerator `Integer` and denominator `Integer`.",
                (&'a Integer, &'a Integer) }

from! { "a `u32`.", u32 }
from! { "an `i32`.", i32 }
from! { "a numerator `u32` and denominator `u32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (u32, u32) }
from! { "a numerator `i32` and denominator `u32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (i32, u32) }
from! { "a numerator `u32` and denominator `i32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (u32, i32) }
from! { "a numerator `i32` and denominator `i32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (i32, i32) }

impl<'a> Assign<&'a Rational> for Rational {
    /// Assigns from another `Rational` number.
    fn assign(&mut self, other: &'a Rational) {
        unsafe {
            gmp::mpq_set(&mut self.inner, &other.inner);
        }
    }
}

impl Assign for Rational {
    /// Assigns from another `Rational` number.
    fn assign(&mut self, mut other: Rational) {
        self.assign(&other);
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Integer> for Rational {
    /// Assigns from an `Integer`.
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(&mut self.inner, integer_inner(val));
        }
    }
}

impl Assign<Integer> for Rational {
    /// Assigns from an `Integer`.
    fn assign(&mut self, mut val: Integer) {
        let numer =
            unsafe { &mut *(gmp::mpq_numref(&mut self.inner) as *mut Integer) };
        let denom =
            unsafe { &mut *(gmp::mpq_numref(&mut self.inner) as *mut Integer) };
        mem::swap(numer, &mut val);
        denom.assign(1);
    }
}

macro_rules! assign_frac {
    { $d:expr, $T1:ty, $T2:ty } => {
        impl Assign<($T1, $T2)> for Rational {
            /// Assigns from
            #[doc=$d]
            ///
            /// # Panics
            ///
            /// Panics if the denominator is zero.
            fn assign(&mut self, (num, den): ($T1, $T2)) {
                let num_den = self.as_mut_numer_denom();
                num_den.0.assign(num);
                num_den.1.assign(den);
            }
        }
    };
}

assign_frac! { "a numerator `Integer` and a denominator `Integer`.",
                Integer, Integer }

impl<'a> Assign<(&'a Integer, &'a Integer)> for Rational {
    /// Assigns from a numerator `Integer` and a denominator `Integer`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (&Integer, &Integer)) {
        let num_den = self.as_mut_numer_denom();
        num_den.0.assign(num);
        num_den.1.assign(den);
    }
}

impl Assign<u32> for Rational {
    /// Assigns from a `u32`.
    fn assign(&mut self, val: u32) {
        self.assign((val, 1u32));
    }
}

impl Assign<i32> for Rational {
    /// Assigns from an `i32`.
    fn assign(&mut self, val: i32) {
        self.assign((val, 1i32));
    }
}

assign_frac! { "a numerator `u32` and a denominator `u32`.", u32, u32 }
assign_frac! { "a numerator `i32` and a denominator `u32`.", i32, u32 }
assign_frac! { "a numerator `u32` and a denominator `i32`.", u32, i32 }
assign_frac! { "a numerator `i32` and a denominator `i32`.", i32, i32 }

impl<'a> Assign<&'a Rational> for Integer {
    /// Assigns from a `Rational` number, rounding towards zero.
    fn assign(&mut self, val: &'a Rational) {
        unsafe {
            gmp::mpz_set_q(integer_inner_mut(self), &val.inner);
        }
    }
}

impl<'a> Assign<Rational> for Integer {
    /// Assigns from a `Rational` number, rounding towards zero.
    fn assign(&mut self, val: Rational) {
        self.assign(&val);
    }
}

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Inter: ident
    } => {
        impl<'a> $Imp<&'a Rational> for Rational {
            type Output = Rational;
            fn $method(mut self, op: &'a Rational) -> Rational {
                self.$method_assign(op);
                self
            }
        }

        impl $Imp<Rational> for Rational {
            type Output = Rational;
            fn $method(self, op: Rational) -> Rational {
                self.$method(&op)
            }
        }

        impl<'a> $ImpAssign<&'a Rational> for Rational {
            fn $method_assign(&mut self, op: &'a Rational) {
                unsafe {
                    $func(&mut self.inner, &self.inner, &op.inner);
                }
            }
        }

        impl $ImpAssign<Rational> for Rational {
            fn $method_assign(&mut self, op: Rational) {
                self.add_assign(&op);
            }
        }

        impl<'a> $Imp<&'a Rational> for &'a Rational {
            /// An intermediate value.
            type Output = $Inter<'a>;
            /// Creates an intermediate value.
            fn $method(self, rhs: &'a Rational) -> $Inter<'a> {
                $Inter {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        /// This is actually private, this documentation should not be
        /// visible.
        pub struct $Inter<'a> {
            lhs: &'a Rational,
            rhs: &'a Rational,
        }

        impl<'a> Assign<$Inter<'a>> for Rational {
            fn assign(&mut self, rhs: $Inter) {
                unsafe {
                    $func(&mut self.inner, &rhs.lhs.inner, &rhs.rhs.inner);
                }
            }
        }

        from_borrow! { "an intermediate value.", $Inter<'a> }
    };
}

macro_rules! arith_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $func:path,
        $Inter:ident
    } => {
        arith_binary! { $Imp $method,
                        $ImpAssign $method_assign,
                        $func,
                        $Inter }

        impl<'a> $ImpFromAssign<&'a Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: &'a Rational) {
                unsafe {
                    $func(&mut self.inner, &lhs.inner, &self.inner);
                }
            }
        }

        impl $ImpFromAssign<Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: Rational) {
                self.$method_from_assign(&lhs);
            }
        }

    };
}

arith_binary! { Add add, AddAssign add_assign, gmp::mpq_add, AddInter }
arith_noncommut! { Sub sub,
                   SubAssign sub_assign,
                   SubFromAssign sub_from_assign,
                   gmp::mpq_sub,
                   SubInter }
arith_binary! { Mul mul, MulAssign mul_assign, gmp::mpq_mul, MulInter }
arith_noncommut! { Div div,
                   DivAssign div_assign,
                   DivFromAssign div_from_assign,
                   gmp::mpq_div,
                   DivInter }

impl Neg for Rational {
    type Output = Rational;
    fn neg(mut self) -> Rational {
        self.neg_assign();
        self
    }
}

impl NegAssign for Rational {
    fn neg_assign(&mut self) {
        unsafe {
            gmp::mpq_neg(&mut self.inner, &self.inner);
        }
    }
}

impl<'a> Neg for &'a Rational {
    /// An intermediate value.
    type Output = NegInter<'a>;
    /// Creates an intermediate value.
    fn neg(self) -> NegInter<'a> {
        NegInter { op: self }
    }
}

/// This is actually private, this documentation should not be
/// visible.
pub struct NegInter<'a> {
    op: &'a Rational,
}

impl<'a> Assign<NegInter<'a>> for Rational {
    fn assign(&mut self, rhs: NegInter) {
        unsafe {
            gmp::mpq_neg(&mut self.inner, &rhs.op.inner);
        }
    }
}

from_borrow! { "an intermediate value.", NegInter<'a> }

macro_rules! arith_prim {
    ($Imp:ident $method:ident,
     $ImpAssign:ident $method_assign:ident,
     $T:ty,
     $func:path,
     $Inter:ident) => {
        impl $Imp<$T> for Rational {
            type Output = Rational;
            fn $method(mut self, op: $T) -> Rational {
                self.$method_assign(op);
                self
            }
        }

        impl $ImpAssign<$T> for Rational {
            fn $method_assign(&mut self, op: $T) {
                unsafe {
                    $func(&mut self.inner, &self.inner, op.into());
                }
            }
        }

        impl<'a> $Imp<$T> for &'a Rational {
            /// An intermediate value.
            type Output = $Inter<'a>;
            /// Creates an intermediate value.
            fn $method(self, op: $T) -> $Inter<'a> {
                $Inter {
                    lhs: self,
                    rhs: op,
                }
            }
        }

        /// This is actually private, this documentation should not be
        /// visible.
        pub struct $Inter<'a> {
            lhs: &'a Rational,
            rhs: $T,
        }

        impl<'a> Assign<$Inter<'a>> for Rational {
            fn assign(&mut self, rhs: $Inter) {
                unsafe {
                    $func(&mut self.inner, &rhs.lhs.inner, rhs.rhs.into());
                }
            }
        }

        from_borrow! { "an intermediate value.", $Inter<'a> }
    };
}

arith_prim! { Shl shl,
              ShlAssign shl_assign,
              u32,
              gmp::mpq_mul_2exp,
              ShlInterU32 }
arith_prim! { Shr shr,
              ShrAssign shr_assign,
              u32,
              gmp::mpq_div_2exp,
              ShrInterU32 }
arith_prim! { Pow pow, PowAssign pow_assign, u32, mpq_pow_ui, PowInterU32 }
arith_prim! { Shl shl, ShlAssign shl_assign, i32, mpq_mul_2exp_si, ShlInterI32 }
arith_prim! { Shr shr, ShrAssign shr_assign, i32, mpq_div_2exp_si, ShrInterI32 }
arith_prim! { Pow pow, PowAssign pow_assign, i32, mpq_pow_si, PowInterI32 }

unsafe fn mpq_mul_2exp_si(rop: *mut gmp::mpq_t,
                          op1: *const gmp::mpq_t,
                          op2: c_long) {
    if op2 >= 0 {
        gmp::mpq_mul_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpq_div_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

unsafe fn mpq_div_2exp_si(rop: *mut gmp::mpq_t,
                          op1: *const gmp::mpq_t,
                          op2: c_long) {
    if op2 >= 0 {
        gmp::mpq_div_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpq_mul_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

unsafe fn mpq_pow_ui(rop: *mut gmp::mpq_t,
                     op1: *const gmp::mpq_t,
                     op2: c_ulong) {
    let rop_num = gmp::mpq_numref(rop);
    let rop_den = gmp::mpq_denref(rop);
    let op1_num = gmp::mpq_numref(op1 as *mut _) as *const _;
    let op1_den = gmp::mpq_denref(op1 as *mut _) as *const _;
    gmp::mpz_pow_ui(rop_num, op1_num, op2);
    gmp::mpz_pow_ui(rop_den, op1_den, op2);
}

unsafe fn mpq_pow_si(rop: *mut gmp::mpq_t,
                     op1: *const gmp::mpq_t,
                     op2: c_long) {
    if op2 < 0 {
        assert_ne!(gmp::mpq_sgn(op1), 0, "division by zero");
        gmp::mpq_inv(rop, op1);
        mpq_pow_ui(rop, rop, op2.wrapping_neg() as c_ulong);
    } else {
        mpq_pow_ui(rop, op1, op2 as c_ulong);
    };
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(&self.inner, &other.inner) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(&self.inner, &other.inner) != 0 }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $T:ty, $eval:expr } => {
        impl PartialEq<$T> for Rational {
            fn eq(&self, other: &$T) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Rational {
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                Some($eval(&self.inner, other))
            }
        }

        impl PartialEq<Rational> for $T {
            fn eq(&self, other: &Rational) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<Rational> for $T {
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                match other.partial_cmp(self) {
                    Some(x) => Some(x.reverse()),
                    None => None,
                }
            }
        }
    }
}

cmp! { Integer, |r, t| unsafe { gmp::mpq_cmp_z(r, integer_inner(t)).cmp(&0) } }
cmp! { u32, |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1).cmp(&0) } }
cmp! { i32, |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1).cmp(&0) } }

cmp! { (u32, u32), |r, t: &(u32, u32)| {
    assert_ne!(t.1, 0, "division by zero");
    unsafe { gmp::mpq_cmp_ui(r, t.0.into(), t.1.into()).cmp(&0) }
} }
cmp! { (i32, u32), |r, t: &(i32, u32)| {
    let mut num = (t.0.wrapping_abs() as u32).into();
    let mut den = t.1.into();
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), t.0 < 0) };
    unsafe { gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }
cmp! { (u32, i32), |r, t: &(u32, i32)| {
    let mut num = t.0.into();
    let mut den = (t.1.wrapping_abs() as u32).into();
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), t.1 < 0) };
    unsafe {gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }
cmp! { (i32, i32), |r, t: &(i32, i32)| {
    let mut num = (t.0.wrapping_abs() as u32).into();
    let mut den = (t.1.wrapping_abs() as u32).into();
    let neg = (t.0 < 0) != (t.1 < 0);
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), neg) };
    unsafe { gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }

fn make_string(r: &Rational, radix: i32, to_upper: bool) -> String {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let (num, den) = r.as_numer_denom();
    let n_size = unsafe { gmp::mpz_sizeinbase(integer_inner(num), radix) };
    let d_size = unsafe { gmp::mpz_sizeinbase(integer_inner(den), radix) };
    // n_size + d_size + 3 for '-', '/' and nul
    let size = n_size.checked_add(d_size).unwrap().checked_add(3).unwrap();
    let mut buf = Vec::<u8>::with_capacity(size);
    let case_radix = if to_upper { -radix } else { radix };
    unsafe {
        buf.set_len(size);
        gmp::mpq_get_str(buf.as_mut_ptr() as *mut c_char,
                         case_radix as c_int,
                         &r.inner);
        let nul_index = buf.iter().position(|&x| x == 0).unwrap();
        buf.set_len(nul_index);
        String::from_utf8_unchecked(buf)
    }
}

fn fmt_radix(r: &Rational,
             f: &mut Formatter,
             radix: i32,
             to_upper: bool,
             prefix: &str)
             -> fmt::Result {
    let s = make_string(r, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

impl Display for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Rational {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// An error which can be returned when parsing a `Rational` number.
pub struct ParseRationalError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    InvalidDigit,
    NoDigits,
    NumerNoDigits,
    DenomNoDigits,
    TooManySlashes,
    DenomZero,
}

impl Error for ParseRationalError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidDigit => "invalid digit found in string",
            NoDigits => "string has no digits",
            NumerNoDigits => "string has no digits for numerator",
            DenomNoDigits => "string has no digits for denominator",
            TooManySlashes => "more than one / found in string",
            DenomZero => "string has zero denominator",
        }
    }
}

impl Display for ParseRationalError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

/// Used to borrow the numerator and denominator of a
/// [`Rational`](struct.Rational.html) number mutably.
///
/// The `Rational` number is canonicalized when the borrow ends. See
/// the [`Rational::as_mut_numer_denom()`]
/// (struct.Rational.html#method.as_mut_numer_denom) method.
pub struct MutNumerDenom<'a>(pub &'a mut Integer, pub &'a mut Integer);

impl<'a> Drop for MutNumerDenom<'a> {
    fn drop(&mut self) {
        assert_ne!(self.1.sign(), Ordering::Equal, "division by zero");
        unsafe {
            let rat_num = integer_inner_mut(self.0);
            let rat_den = integer_inner_mut(self.1);
            let mut canon: gmp::mpq_t = mem::uninitialized();
            let canon_num_ptr = gmp::mpq_numref(&mut canon);
            let canon_den_ptr = gmp::mpq_denref(&mut canon);
            mem::swap(rat_num, &mut *canon_num_ptr);
            mem::swap(rat_den, &mut *canon_den_ptr);
            gmp::mpq_canonicalize(&mut canon);
            mem::swap(rat_num, &mut *canon_num_ptr);
            mem::swap(rat_den, &mut *canon_den_ptr);
        }
    }
}

fn integer_inner(z: &Integer) -> &gmp::mpz_t {
    let ptr = z as *const _ as *const gmp::mpz_t;
    unsafe { &*ptr }
}

// This is unsafe as it returns a structure which can be used to break
// the state of z.
unsafe fn integer_inner_mut(z: &mut Integer) -> &mut gmp::mpz_t {
    let ptr = z as *mut _ as *mut gmp::mpz_t;
    &mut *ptr
}

// The return struct has pointers to the given limbs, so no
// deallocation must take place. This function panics if limbs.1 is 0,
// so there is no need to check before calling it.
unsafe fn single_limbs(limbs: (&mut gmp::limb_t, &mut gmp::limb_t),
                       neg: bool)
                       -> gmp::mpq_t {
    assert_ne!(*limbs.1, 0, "division by zero");
    let mut ret = mem::uninitialized();
    *gmp::mpq_numref(&mut ret) = gmp::mpz_t {
        alloc: 1,
        d: limbs.0,
        size: if *limbs.0 == 0 {
            0
        } else if neg {
            -1
        } else {
            1
        },
    };
    *gmp::mpq_denref(&mut ret) = gmp::mpz_t {
        alloc: 1,
        d: limbs.1,
        size: 1,
    };
    gmp::mpq_canonicalize(&mut ret);
    ret
}

#[cfg(test)]
mod tests {
    use rational::*;
    use std::{i32, u32};

    #[test]
    fn check_ref_op() {
        let lhs = Rational::from((-13, 27));
        let rhs = Rational::from((15, 101));
        let pu = 30_u32;
        let pi = -15_i32;
        assert!(Rational::from(-&lhs) == -lhs.clone());
        assert!(Rational::from(&lhs + &rhs) == lhs.clone() + &rhs);
        assert!(Rational::from(&lhs - &rhs) == lhs.clone() - &rhs);
        assert!(Rational::from(&lhs * &rhs) == lhs.clone() * &rhs);
        assert!(Rational::from(&lhs / &rhs) == lhs.clone() / &rhs);

        assert!(Rational::from(&lhs << pu) == lhs.clone() << pu);
        assert!(Rational::from(&lhs >> pu) == lhs.clone() >> pu);
        assert!(Rational::from((&lhs).pow(pu)) == lhs.clone().pow(pu));

        assert!(Rational::from(&lhs << pi) == lhs.clone() << pi);
        assert!(Rational::from(&lhs >> pi) == lhs.clone() >> pi);
        assert!(Rational::from((&lhs).pow(pi)) == lhs.clone().pow(pi));
    }

    #[test]
    fn check_cmp_frac() {
        let zero = Rational::new();
        let u = [0, 1, 100, u32::MAX];
        let s = [i32::MIN, -100, -1, 0, 1, 100, i32::MAX];
        for &n in &u {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
        }
        for &n in &s {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
        }
    }

    #[test]
    fn check_from_str() {
        let bad_strings = [(" 1", None),
                           ("1/-1", None),
                           ("1/+3", None),
                           ("1/0", None),
                           ("1 / 1", None),
                           ("2/", None),
                           ("/2", None),
                           ("++1", None),
                           ("+-1", None),
                           ("1/80", Some(8)),
                           ("0xf", Some(16)),
                           ("9", Some(9))];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Rational::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings = [("0", 10, 0, 1),
                            ("+0/fC", 16, 0, 1),
                            ("-0/10", 2, 0, 1),
                            ("-99/3", 10, -33, 1),
                            ("+Ce/fF", 16, 0xce, 0xff),
                            ("-77/2", 8, -0o77, 2)];
        for &(s, radix, n, d) in good_strings.into_iter() {
            let r = Rational::from_str_radix(s, radix).unwrap();
            assert!(*r.numer() == n);
            assert!(*r.denom() == d);
        }
    }

    #[test]
    fn check_formatting() {
        let r = Rational::from((-11, 15));
        assert!(format!("{}", r) == "-11/15");
        assert!(format!("{:?}", r) == "-11/15");
        assert!(format!("{:b}", r) == "-1011/1111");
        assert!(format!("{:#b}", r) == "-0b1011/1111");
        assert!(format!("{:o}", r) == "-13/17");
        assert!(format!("{:#o}", r) == "-0o13/17");
        assert!(format!("{:x}", r) == "-b/f");
        assert!(format!("{:X}", r) == "-B/F");
        assert!(format!("{:8x}", r) == "    -b/f");
        assert!(format!("{:08X}", r) == "-0000B/F");
        assert!(format!("{:#08x}", r) == "-0x00b/f");
        assert!(format!("{:#8X}", r) == "  -0xB/F");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert!(gmp::NAIL_BITS == 0);
        assert!(gmp::NUMB_BITS == gmp::LIMB_BITS);
        assert!(gmp::NUMB_BITS as usize == 8 * mem::size_of::<gmp::limb_t>());
    }
}
