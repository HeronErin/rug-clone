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

use {Assign, DivFromAssign, NegAssign, NotAssign, Pow, PowAssign,
     RemFromAssign, SubFromAssign};
use gmp_mpfr_sys::gmp::{self, mpz_t};
#[cfg(feature = "random")]
use rand::Rng;
use std::{i32, u32};
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CString;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::mem;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
               BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg, Not,
               Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
use std::ptr;
#[cfg(feature = "random")]
use std::slice;
use std::str::FromStr;
use xgmp;

/// An arbitrary-precision integer.
///
/// Standard arithmetic operations, bitwise operations and comparisons
/// are supported. In standard arithmetic operations such as addition,
/// you can mix `Integer` and primitive integer types; the result will
/// be an `Integer`.
///
/// Internally the integer is not stored using two's-complement
/// representation, however, for bitwise operations and shifts, the
/// functionality is the same as if the representation was using two's
/// complement.
///
/// # Examples
///
/// ```rust
/// use rugint::Integer;
///
/// let mut i = Integer::from(1);
/// i = i << 1000;
/// // i is now 1000000... (1000 zeros)
/// assert!(i.significant_bits() == 1001);
/// assert!(i.find_one(0) == Some(1000));
/// i -= 1;
/// // i is now 111111... (1000 ones)
/// assert!(i.count_ones() == Some(1000));
///
/// let a = Integer::from(0xf00d);
/// let all_ones_xor_a = Integer::from(-1) ^ &a;
/// // a is unchanged as we borrowed it
/// let complement_a = !a;
/// // now a has been moved, so this would cause an error:
/// // assert!(a > 0);
/// assert!(all_ones_xor_a == complement_a);
/// assert!(complement_a == -0xf00e);
/// assert!(format!("{:x}", complement_a) == "-f00e");
/// ```
pub struct Integer {
    inner: mpz_t,
}

impl Drop for Integer {
    fn drop(&mut self) {
        unsafe {
            gmp::mpz_clear(self.inner_mut());
        }
    }
}

impl Default for Integer {
    fn default() -> Integer {
        Integer::new()
    }
}

impl Clone for Integer {
    fn clone(&self) -> Integer {
        let mut ret = Integer::new();
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Integer) {
        self.assign(source);
    }
}

macro_rules! math_op1 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr])*
        pub fn $method(&mut self $(, $param: $T)*) -> &mut Integer {
            unsafe {
                $func(self.inner_mut(), self.inner() $(, $param.into(),)*);
            }
            self
        }

        $(#[$attr_hold])*
        pub fn $method_hold(&self $(, $param: $T)*) -> $Hold {
            $Hold {
                val: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! math_op1_2 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr])*
        pub fn $method(&mut self, other: &mut Integer $(, $param: $T)*) {
            unsafe {
                $func(self.inner_mut(), other.inner_mut(),
                      self.inner() $(, $param.into())*);
            }
        }

        $(#[$attr_hold])*
        pub fn $method_hold(&self $(, $param: $T)*) -> $Hold {
            $Hold {
                val: self,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! math_op2 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr])*
        pub fn $method(&mut self, other: &Integer $(, $param: $T)*)
                       -> &mut Integer {
            unsafe {
                $func(self.inner_mut(), self.inner(),
                      other.inner() $(, $param.into(),)*);
            }
            self
        }

        $(#[$attr_hold])*
        pub fn $method_hold<'a>(&'a self, other: &'a Integer $(, $param: $T)*)
                                -> $Hold<'a> {
            $Hold {
                lhs: self,
                rhs: other,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! math_op2_2 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr])*
        pub fn $method(&mut self, op: &mut Integer $(, $param: $T)*) {
            unsafe {
                $func(self.inner_mut(), op.inner_mut(),
                      self.inner(), op.inner() $(, $param.into())*);
            }
        }

        $(#[$attr_hold])*
        pub fn $method_hold<'a>(&'a self, other: &'a Integer $(, $param: $T)*)
                                -> $Hold<'a> {
            $Hold {
                lhs: self,
                rhs: other,
                $($param: $param,)*
            }
        }
    };
}

macro_rules! math_op3 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr])*
        pub fn $method(&mut self, op2: &Integer, op3: &Integer $(, $param: $T)*)
                       -> &mut Integer {
            unsafe {
                $func(self.inner_mut(), self.inner(),
                      op2.inner(), op3.inner() $(, $param.into(),)*);
            }
            self
        }

        $(#[$attr_hold])*
        pub fn $method_hold<'a>(&'a self, op2: &'a Integer,
                                op3: &'a Integer $(, $param: $T)*)
                                -> $Hold<'a> {
            $Hold {
                op1: self,
                op2: op2,
                op3: op3,
                $($param: $param,)*
            }
        }
    };
}

impl Integer {
    /// Constructs a new arbitrary-precision integer with value 0.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::new();
    /// assert!(i == 0);
    /// ```
    pub fn new() -> Integer {
        unsafe {
            let mut inner: mpz_t = mem::uninitialized();
            gmp::mpz_init(&mut inner);
            Integer { inner: inner }
        }
    }

    /// Converts to a `u32` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(1234567890);
    /// assert!(fits.to_u32() == Some(1234567890));
    /// let neg = Integer::from(-1);
    /// assert!(neg.to_u32() == None);
    /// let large = "123456789012345".parse::<Integer>().unwrap();
    /// assert!(large.to_u32() == None);
    /// ```
    pub fn to_u32(&self) -> Option<u32> {
        if unsafe { xgmp::mpz_fits_u32(self.inner()) } {
            Some(self.to_u32_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `u32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(0x90abcdef_u32);
    /// assert!(fits.to_u32_wrapping() == 0x90abcdef);
    /// let neg = Integer::from(-1);
    /// assert!(neg.to_u32_wrapping() == 0xffffffff);
    /// let large = Integer::from_str_radix("1234567890abcdef", 16).unwrap();
    /// assert!(large.to_u32_wrapping() == 0x90abcdef);
    /// ```
    pub fn to_u32_wrapping(&self) -> u32 {
        let u = unsafe { xgmp::mpz_get_abs_u32(self.inner()) };
        if self.sign() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to an `i32` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(-50);
    /// assert!(fits.to_i32() == Some(-50));
    /// let small = Integer::from(-123456789012345_i64);
    /// assert!(small.to_i32() == None);
    /// let large = Integer::from(123456789012345_u64);
    /// assert!(large.to_i32() == None);
    /// ```
    pub fn to_i32(&self) -> Option<i32> {
        if unsafe { xgmp::mpz_fits_i32(self.inner()) } {
            Some(self.to_i32_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `i32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(-0xabcdef_i32);
    /// assert!(fits.to_i32_wrapping() == -0xabcdef);
    /// let small = Integer::from(0x1_ffff_ffff_u64);
    /// assert!(small.to_i32_wrapping() == -1);
    /// let large = Integer::from_str_radix("1234567890abcdef", 16).unwrap();
    /// assert!(large.to_i32_wrapping() == 0x90abcdef_u32 as i32);
    /// ```
    pub fn to_i32_wrapping(&self) -> i32 {
        self.to_u32_wrapping() as i32
    }

    /// Converts to a `u64` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(123456789012345_u64);
    /// assert!(fits.to_u64() == Some(123456789012345));
    /// let neg = Integer::from(-1);
    /// assert!(neg.to_u64() == None);
    /// let large = "1234567890123456789012345".parse::<Integer>().unwrap();
    /// assert!(large.to_u64() == None);
    /// ```
    pub fn to_u64(&self) -> Option<u64> {
        if unsafe { xgmp::mpz_fits_u64(self.inner()) } {
            Some(self.to_u64_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `u64`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(0x90abcdef_u64);
    /// assert!(fits.to_u64_wrapping() == 0x90abcdef);
    /// let neg = Integer::from(-1);
    /// assert!(neg.to_u64_wrapping() == 0xffff_ffff_ffff_ffff);
    /// let large = Integer::from_str_radix("f123456789abcdef0", 16).unwrap();
    /// assert!(large.to_u64_wrapping() == 0x123456789abcdef0);
    /// ```
    pub fn to_u64_wrapping(&self) -> u64 {
        let u = unsafe { xgmp::mpz_get_abs_u64(self.inner()) };
        if self.sign() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to an `i64` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(-50);
    /// assert!(fits.to_i64() == Some(-50));
    /// let small = Integer::from_str_radix("-fedcba9876543210", 16).unwrap();
    /// assert!(small.to_i64() == None);
    /// let large = Integer::from_str_radix("fedcba9876543210", 16).unwrap();
    /// assert!(large.to_i64() == None);
    /// ```
    pub fn to_i64(&self) -> Option<i64> {
        if unsafe { xgmp::mpz_fits_i64(self.inner()) } {
            Some(self.to_i64_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `i64`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rugint::Integer;
    /// let fits = Integer::from(-0xabcdef);
    /// assert!(fits.to_i64_wrapping() == -0xabcdef);
    /// let small = Integer::from_str_radix("1ffffffffffffffff", 16).unwrap();
    /// assert!(small.to_i64_wrapping() == -1);
    /// let large = Integer::from_str_radix("f1234567890abcdef", 16).unwrap();
    /// assert!(large.to_i64_wrapping() == 0x1234567890abcdef_i64);
    /// ```
    pub fn to_i64_wrapping(&self) -> i64 {
        self.to_u64_wrapping() as i64
    }

    /// Assigns from an `f64` if it is finite, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// let ret = i.assign_f64(12.7);
    /// assert!(ret.is_ok());
    /// assert!(i == 12);
    /// let ret = i.assign_f64(1.0 / 0.0);
    /// assert!(ret.is_err());
    /// assert!(i == 12);
    /// ```
    pub fn assign_f64(&mut self, val: f64) -> Result<(), ()> {
        if val.is_finite() {
            unsafe {
                gmp::mpz_set_d(self.inner_mut(), val);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    /// Creates an `Integer` from an `f64` if it is finite, rounding
    /// towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::f64;
    /// let i = Integer::from_f64(1e20).unwrap();
    /// assert!(i == "100000000000000000000".parse::<Integer>().unwrap());
    /// let inf = Integer::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    pub fn from_f64(val: f64) -> Option<Integer> {
        if val.is_finite() {
            unsafe {
                let mut inner: mpz_t = mem::uninitialized();
                gmp::mpz_init_set_d(&mut inner, val);
                Some(Integer { inner: inner })
            }
        } else {
            None
        }
    }

    /// Converts to an `f64`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::f64;
    ///
    /// // An `f64` has 53 bits of precision.
    /// let exact = 0x1f_ffff_ffff_ffff_u64;
    /// let i = Integer::from(exact);
    /// assert!(i.to_f64() == exact as f64);
    ///
    /// // large has 56 ones
    /// let large = 0xff_ffff_ffff_ffff_u64;
    /// // trunc has 53 ones followed by 3 zeros
    /// let trunc = 0xff_ffff_ffff_fff8_u64;
    /// let j = Integer::from(large);
    /// assert!(j.to_f64() == trunc as f64);
    ///
    /// let max = Integer::from_f64(f64::MAX).unwrap();
    /// let plus_one = max + 1u32;
    /// // plus_one is truncated to f64::MAX
    /// assert!(plus_one.to_f64() == f64::MAX);
    /// let times_two = plus_one * 2u32;
    /// // times_two is too large
    /// assert!(times_two.to_f64() == f64::INFINITY);
    /// ```
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpz_get_d(self.inner()) }
    }

    /// Assigns from an `f32` if it is finite, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::f32;
    /// let mut i = Integer::new();
    /// let ret = i.assign_f64(-12.7);
    /// assert!(ret.is_ok());
    /// assert!(i == -12);
    /// let ret = i.assign_f32(f32::NAN);
    /// assert!(ret.is_err());
    /// assert!(i == -12);
    /// ```
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val as f64)
    }

    /// Creates an `Integer` from an `f32` if it is finite, rounding
    /// towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::f32;
    /// let i = Integer::from_f32(-5.6).unwrap();
    /// assert!(i == -5);
    /// let neg_inf = Integer::from_f32(f32::NEG_INFINITY);
    /// assert!(neg_inf.is_none());
    /// ```
    pub fn from_f32(val: f32) -> Option<Integer> {
        Integer::from_f64(val as f64)
    }

    /// Converts to an `f32`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::f32;
    /// let min = Integer::from_f32(f32::MIN).unwrap();
    /// let minus_one = min - 1u32;
    /// // minus_one is truncated to f32::MIN
    /// assert!(minus_one.to_f32() == f32::MIN);
    /// let times_two = minus_one * 2u32;
    /// // times_two is too small
    /// assert!(times_two.to_f32() == f32::NEG_INFINITY);
    /// ```
    pub fn to_f32(&self) -> f32 {
        let f = self.to_f64();
        // f as f32 might round away from zero, so we need to clear
        // the least significant bits of f.
        // * If f is a nan, we do NOT want to clear any mantissa bits,
        //   as this may change f into +/- infinity.
        // * If f is +/- infinity, the bits are already zero, so the
        //   masking has no effect.
        // * If f is subnormal, f as f32 will be zero anyway.
        if !f.is_nan() {
            let u = unsafe { mem::transmute::<_, u64>(f) };
            // f64 has 29 more significant bits than f32.
            let trunc_u = u & (!0 << 29);
            let trunc_f = unsafe { mem::transmute::<_, f64>(trunc_u) };
            trunc_f as f32
        } else {
            f as f32
        }
    }

    /// Returns a string representation of `self` for the specified
    /// `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// let mut i = Integer::new();
    /// assert!(i.to_string_radix(10) == "0");
    /// i.assign(-10);
    /// assert!(i.to_string_radix(16) == "-a");
    /// i.assign(0x1234cdef);
    /// assert!(i.to_string_radix(4) == "102031030313233");
    /// i.assign_str_radix("1234567890aAbBcCdDeEfF", 16).unwrap();
    /// assert!(i.to_string_radix(16) == "1234567890aabbccddeeff");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self, radix: i32) -> String {
        make_string(self, radix, false)
    }

    /// Parses an `Integer`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from_str_radix("-ff", 16).unwrap();
    /// assert!(i == -0xff);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str,
                          radix: i32)
                          -> Result<Integer, ParseIntegerError> {
        let mut i = Integer::new();
        i.assign_str_radix(src, radix)?;
        Ok(i)
    }

    /// Parses an `Integer` from a string in decimal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str("123").unwrap();
    /// assert!(i == 123);
    /// let ret = i.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseIntegerError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses an `Integer` from a string with the specified radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str_radix("ff", 16).unwrap();
    /// assert!(i == 0xff);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ParseIntegerError> {
        let s = check_str_radix(src, radix)?;
        let c_str = CString::new(s).unwrap();
        let err = unsafe {
            gmp::mpz_set_str(self.inner_mut(), c_str.as_ptr(), radix.into())
        };
        assert_eq!(err, 0);
        Ok(())
    }

    /// Checks if an `Integer` can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses an `Integer`. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::valid_str_radix("123", 4).is_ok());
    /// assert!(Integer::valid_str_radix("123xyz", 36).is_ok());
    ///
    /// let invalid_valid = Integer::valid_str_radix("123", 3);
    /// let invalid_from = Integer::from_str_radix("123", 3);
    /// assert!(invalid_valid.unwrap_err() == invalid_from.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(src: &str,
                           radix: i32)
                           -> Result<(), ParseIntegerError> {
        check_str_radix(src, radix).map(|_| ())
    }

    /// Returns `true` if `self` is divisible by `divisor`. Unlike
    /// other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(230);
    /// assert!(i.is_divisible(&Integer::from(10)));
    /// assert!(!i.is_divisible(&Integer::from(100)));
    /// assert!(!i.is_divisible(&Integer::new()));
    /// ```
    pub fn is_divisible(&self, divisor: &Integer) -> bool {
        unsafe { gmp::mpz_divisible_p(self.inner(), divisor.inner()) != 0 }
    }

    /// Returns `true` if `self` is divisible by `divisor`. Unlike
    /// other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(230);
    /// assert!(i.is_divisible_u(23));
    /// assert!(!i.is_divisible_u(100));
    /// assert!(!i.is_divisible_u(0));
    /// ```
    pub fn is_divisible_u(&self, divisor: u32) -> bool {
        unsafe { gmp::mpz_divisible_ui_p(self.inner(), divisor.into()) != 0 }
    }

    /// Returns `true` if `self` is divisible by two to the power of
    /// `b`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(15 << 17);
    /// assert!(i.is_divisible_2pow(16));
    /// assert!(i.is_divisible_2pow(17));
    /// assert!(!i.is_divisible_2pow(18));
    /// ```
    pub fn is_divisible_2pow(&self, b: u32) -> bool {
        unsafe { gmp::mpz_divisible_2exp_p(self.inner(), b.into()) != 0 }
    }

    /// Returns `true` if `self` is congruent to `c` modulo `divisor`, that
    /// is, if there exists a `q` such that `self == c + q * divisor`.
    /// Unlike other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let n = Integer::from(105);
    /// let divisor = Integer::from(10);
    /// assert!(n.is_congruent(&Integer::from(5), &divisor));
    /// assert!(n.is_congruent(&Integer::from(25), &divisor));
    /// assert!(!n.is_congruent(&Integer::from(7), &divisor));
    /// // n is congruent to itself if divisor is 0
    /// assert!(n.is_congruent(&n, &Integer::from(0)));
    /// ```
    pub fn is_congruent(&self, c: &Integer, divisor: &Integer) -> bool {
        unsafe {
            gmp::mpz_congruent_p(self.inner(), c.inner(), divisor.inner()) != 0
        }
    }

    /// Returns `true` if `self` is congruent to `c` modulo `divisor`, that
    /// is, if there exists a `q` such that `self == c + q * divisor`.
    /// Unlike other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let n = Integer::from(105);
    /// assert!(n.is_congruent_u(3335, 10));
    /// assert!(!n.is_congruent_u(107, 10));
    /// // n is congruent to itself if divisor is 0
    /// assert!(n.is_congruent_u(105, 0));
    /// ```
    pub fn is_congruent_u(&self, c: u32, divisor: u32) -> bool {
        unsafe {
            gmp::mpz_congruent_ui_p(self.inner(), c.into(), divisor.into()) != 0
        }
    }

    /// Returns `true` if `self` is congruent to `c` modulo two to the
    /// power of `b`, that is, if there exists a `q` such that `self
    /// == c + q * 2 ^ b`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let n = Integer::from(13 << 17 | 21);
    /// assert!(n.is_congruent_2pow(&Integer::from(7 << 17 | 21), 17));
    /// assert!(!n.is_congruent_2pow(&Integer::from(13 << 17 | 22), 17));
    /// ```
    pub fn is_congruent_2pow(&self, c: &Integer, b: u32) -> bool {
        unsafe {
            gmp::mpz_congruent_2exp_p(self.inner(), c.inner(), b.into()) != 0
        }
    }

    /// Returns `true` if `self` is a perfect power.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// // 0 is 0 to the power of anything
    /// let mut i = Integer::from(0);
    /// assert!(i.is_perfect_power());
    /// // 243 is 3 to the power of 5
    /// i.assign(243);
    /// assert!(i.is_perfect_power());
    /// // 10 is not a perfect power
    /// i.assign(10);
    /// assert!(!i.is_perfect_power());
    /// ```
    pub fn is_perfect_power(&self) -> bool {
        unsafe { gmp::mpz_perfect_power_p(self.inner()) != 0 }
    }

    /// Returns `true` if `self` is a perfect square.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// let mut i = Integer::from(1);
    /// assert!(i.is_perfect_square());
    /// i.assign(9);
    /// assert!(i.is_perfect_square());
    /// i.assign(15);
    /// assert!(!i.is_perfect_square());
    /// ```
    pub fn is_perfect_square(&self) -> bool {
        unsafe { gmp::mpz_perfect_square_p(self.inner()) != 0 }
    }

    math_op2_2! {
        /// Computes the quotient and remainder of `self` divided by
        /// `op`.
        ///
        /// # Panics
        ///
        /// Panics if `op` is zero.
        fn div_rem;
        /// Holds a computation of the quotient and remainder of a
        /// division operation.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(10);
        /// let hold = dividend.div_rem_hold(&divisor);
        /// let mut quotient = Integer::new();
        /// let mut remainder = Integer::new();
        /// (&mut quotient, &mut remainder).assign(hold);
        /// assert!(quotient == 2);
        /// assert!(remainder == 3);
        /// ```
        fn div_rem_hold -> DivRemHold;
        xgmp::mpz_tdiv_qr_check_0
    }
    math_op1! {
        /// Computes the absolute value of `self`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(-100);
        /// assert!(*i.abs() == 100);
        /// assert!(i == 100);
        /// ```
        fn abs;
        /// Holds a computation of the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let i = Integer::from(-100);
        /// let hold = i.abs_hold();
        /// let abs = Integer::from(hold);
        /// assert!(abs == 100);
        /// ```
        fn abs_hold -> AbsHold;
        gmp::mpz_abs
    }
    math_op2! {
        /// Divides `self` by `other`. This is much faster than normal
        /// division, but produces correct results only when the division
        /// is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(123450);
        /// assert!(*i.div_exact(&Integer::from(10)) == 12345);
        /// assert!(i == 12345);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `other` is zero.
        fn div_exact;
        /// Holds a computation of an exact division.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let i = Integer::from(123450);
        /// let divisor = Integer::from(10);
        /// let hold = i.div_exact_hold(&divisor);
        /// let q = Integer::from(hold);
        /// assert!(q == 12345);
        /// ```
        fn div_exact_hold -> DivExactHold;
        xgmp::mpz_divexact_check_0
    }
    math_op1! {
        /// Divides `self` by `divisor`. This is much faster than normal
        /// division, but produces correct results only when the division
        /// is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(123450);
        /// assert!(*i.div_exact_u(10) == 12345);
        /// assert!(i == 12345);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_exact_u;
        /// Holds a computation of an exact division.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let i = Integer::from(123450);
        /// let hold = i.div_exact_u_hold(10);
        /// let q = Integer::from(hold);
        /// assert!(q == 12345);
        /// ```
        fn div_exact_u_hold -> DivExactUHold;
        xgmp::mpz_divexact_ui_check_0,
        divisor: u32
    }
    math_op3! {
        /// Raises `self` to the power of `op2` modulo `op3`. If `op2`
        /// is negative, then `self` must have an inverse modulo
        /// `op3`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        ///
        /// // 7 ^ 5 = 16807
        /// let mut n = Integer::from(7);
        /// let pow = Integer::from(5);
        /// let m = Integer::from(1000);
        /// assert!(*n.pow_mod(&pow, &m) == 807);
        ///
        /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
        /// // 143 ^ 5 modulo 1000 = 943.
        /// n.assign(7);
        /// let neg_pow = Integer::from(-5);
        /// assert!(*n.pow_mod(&neg_pow, &m) == 943);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `op2` is negative and `self` does not have an
        /// inverse modulo `op3`.
        fn pow_mod;
        /// Holds the computation of raising to the power of `op2`
        /// modulo `op3`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// // 7 ^ 5 = 16807
        /// let base = Integer::from(7);
        /// let pow = Integer::from(5);
        /// let m = Integer::from(1000);
        /// let hold = base.pow_mod_hold(&pow, &m);
        /// assert!(Integer::from(hold) == 807);
        /// ```
        fn pow_mod_hold -> PowModHold;
        xgmp::mpz_powm_check_inverse
    }

    /// Raises `base` to the power of `power`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 12);
    /// assert!(i == 13_u64.pow(12));
    /// ```
    pub fn assign_u_pow_u(&mut self, base: u32, power: u32) {
        unsafe {
            gmp::mpz_ui_pow_ui(self.inner_mut(), base.into(), power.into());
        }
    }

    /// Raises `base` to the power of `power`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_i_pow_u(-13, 12);
    /// assert!(i == (-13_i64).pow(12));
    /// i.assign_i_pow_u(-13, 13);
    /// assert!(i == (-13_i64).pow(13));
    /// ```
    pub fn assign_i_pow_u(&mut self, base: i32, power: u32) {
        if base >= 0 {
            self.assign_u_pow_u(base as u32, power);
        } else {
            self.assign_u_pow_u(base.wrapping_neg() as u32, power);
            if (power & 1) == 1 {
                self.neg_assign();
            }
        }
    }

    math_op1! {
        /// Computes the `n`th root of `self` and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(1004);
        /// assert!(*i.root(3) == 10);
        /// ```
        fn root;
        /// Holds a computation of the `n`th root of the value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let i = Integer::from(1004);
        /// assert!(Integer::from(i.root_hold(3)) == 10);
        /// ```
        fn root_hold -> RootHold;
        gmp::mpz_root,
        n: u32
    }
    math_op1_2! {
        /// Computes the `n`th root of `self` and returns the truncated
        /// root and the remainder. The remainder is `self` minus the
        /// truncated root raised to the power of `n`. The remainder is
        /// stored in `other`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(1004);
        /// let mut rem = Integer::new();
        /// i.root_rem(&mut rem, 3);
        /// assert!(i == 10);
        /// assert!(rem == 4);
        /// ```
        fn root_rem;
        /// Holds a computation of the truncation and remainder of the
        /// `n`th root of `self`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        /// let i = Integer::from(1004);
        /// let hold = Integer::root_rem_hold(&i, 3);
        /// let mut root = Integer::new();
        /// let mut rem = Integer::new();
        /// (&mut root, &mut rem).assign(hold);
        /// assert!(root == 10);
        /// assert!(rem == 4);
        /// ```
        fn root_rem_hold -> RootRemHold;
        gmp::mpz_rootrem,
        n: u32
    }
    math_op1! {
        /// Computes the square root and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(104);
        /// assert!(*i.sqrt() == 10);
        /// ```
        fn sqrt;
        /// Holds a computation of the square root.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let i = Integer::from(104);
        /// assert!(Integer::from(i.sqrt_hold()) == 10);
        /// ```
        fn sqrt_hold -> SqrtHold;
        gmp::mpz_sqrt
    }
    math_op1_2! {
        /// Computes the square root of `self` and returns the truncated
        /// root and the remainder. The remainder is `self` minus the
        /// truncated root squared. The remainder is stored in `other`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let mut i = Integer::from(104);
        /// let mut rem = Integer::new();
        /// i.sqrt_rem(&mut rem);
        /// assert!(i == 10);
        /// assert!(rem == 4);
        /// ```
        fn sqrt_rem;
        /// Holds a computation of the truncation and remainder of the
        /// square root of `self`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        /// let i = Integer::from(104);
        /// let hold = Integer::sqrt_rem_hold(&i);
        /// let mut root = Integer::new();
        /// let mut rem = Integer::new();
        /// (&mut root, &mut rem).assign(hold);
        /// assert!(root == 10);
        /// assert!(rem == 4);
        /// ```
        fn sqrt_rem_hold -> SqrtRemHold;
        gmp::mpz_sqrtrem
    }
    math_op2! {
        /// Finds the greatest common divisor. The result is always
        /// positive except when both inputs are zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        /// let mut a = Integer::new();
        /// let mut b = Integer::new();
        /// a.gcd(&b);
        /// // gcd of 0, 0 is 0
        /// assert!(*a.gcd(&b) == 0);
        /// b.assign(10);
        /// // gcd of 0, 10 is 10
        /// assert!(*a.gcd(&b) == 10);
        /// b.assign(25);
        /// // gcd of 10, 25 is 5
        /// assert!(*a.gcd(&b) == 5);
        /// ```
        fn gcd;
        /// Holds the computation of the greatest common divisor.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let a = Integer::from(100);
        /// let b = Integer::from(125);
        /// let hold = a.gcd_hold(&b);
        /// // gcd of 100, 125 is 25
        /// assert!(Integer::from(hold) == 25);
        /// ```
        fn gcd_hold -> GcdHold;
        gmp::mpz_gcd
    }
    math_op2! {
        /// Finds the least common multiple. The result is always positive
        /// except when one or both inputs are zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::{Assign, Integer};
        /// let mut a = Integer::from(10);
        /// let mut b = Integer::from(25);
        /// // lcm of 10, 25 is 50
        /// assert!(*a.lcm(&b) == 50);
        /// b.assign(0);
        /// // lcm of 50, 0 is 0
        /// assert!(*a.lcm(&b) == 0);
        /// ```
        fn lcm;
        /// Holds the computation of the least common multiple.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// let a = Integer::from(100);
        /// let b = Integer::from(125);
        /// let hold = a.lcm_hold(&b);
        /// // lcm of 100, 125 is 500
        /// assert!(Integer::from(hold) == 500);
        /// ```
        fn lcm_hold -> LcmHold;
        gmp::mpz_lcm
    }

    /// Finds the inverse of `self` modulo `other` and returns `true`
    /// if an inverse exists.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut n = Integer::from(2);
    /// // Modulo 4, 2 has no inverse, there is no x such that 2 * x = 1.
    /// let exists_4 = n.invert(&Integer::from(4));
    /// assert!(!exists_4);
    /// assert!(n == 2);
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// let exists_5 = n.invert(&Integer::from(5));
    /// assert!(exists_5);
    /// assert!(n == 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `other` is zero.
    pub fn invert(&mut self, other: &Integer) -> bool {
        unsafe {
            xgmp::mpz_invert_check_0(self.inner_mut(),
                                     self.inner(),
                                     other.inner()) != 0
        }
    }

    /// Holds a computation of the inverse of `self` modulo `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// let n = Integer::from(2);
    /// // Modulo 4, 2 has no inverse, there is no x such that 2 * x = 1.
    /// let (mut inv_4, mut exists_4) = (Integer::new(), false);
    /// (&mut inv_4, &mut exists_4).assign(n.invert_hold(&Integer::from(4)));
    /// assert!(!exists_4);
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// let (mut inv_5, mut exists_5) = (Integer::new(), false);
    /// (&mut inv_5, &mut exists_5).assign(n.invert_hold(&Integer::from(5)));
    /// assert!(exists_5);
    /// assert!(inv_5 == 3);
    /// ```
    pub fn invert_hold<'a>(&'a self, other: &'a Integer) -> InvertHold<'a> {
        InvertHold {
            lhs: self,
            rhs: other,
        }
    }

    /// Calculates the Jacobi symbol (`self` / `other`).
    pub fn jacobi(&self, other: &Integer) -> i32 {
        unsafe { gmp::mpz_jacobi(self.inner(), other.inner()) as i32 }
    }

    /// Calculates the Legendre symbol (`self` / `other`).
    pub fn legendre(&self, other: &Integer) -> i32 {
        unsafe { gmp::mpz_legendre(self.inner(), other.inner()) as i32 }
    }

    /// Calculates the Jacobi symbol (`self` / `other`) with the
    /// Kronecker extension.
    pub fn kronecker(&self, other: &Integer) -> i32 {
        unsafe { gmp::mpz_kronecker(self.inner(), other.inner()) as i32 }
    }

    /// Removes all occurrences of `factor` from `self`, and returns
    /// the number of occurrences.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 50);
    /// i *= 1000;
    /// let count = i.remove_factor(&Integer::from(13));
    /// assert!(count == 50);
    /// assert!(i == 1000);
    /// ```
    pub fn remove_factor(&mut self, factor: &Integer) -> u32 {
        let cnt = unsafe {
            gmp::mpz_remove(self.inner_mut(), self.inner(), factor.inner())
        };
        assert!(cnt as u32 as gmp::bitcnt_t == cnt, "overflow");
        cnt as u32
    }

    /// Holds the computation of the removal of `factor`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 50);
    /// i *= 1000;
    /// let (mut j, mut count) = (Integer::new(), 0);
    /// (&mut j, &mut count).assign(i.remove_factor_hold(&Integer::from(13)));
    /// assert!(count == 50);
    /// assert!(j == 1000);
    /// ```
    pub fn remove_factor_hold<'a>(&'a self,
                                  factor: &'a Integer)
                                  -> RemoveFactorHold<'a> {
        RemoveFactorHold {
            lhs: self,
            rhs: factor,
        }
    }

    /// Computes the factorial of `n`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
    /// i.assign_factorial(10);
    /// assert!(i == 3628800);
    /// ```
    pub fn assign_factorial(&mut self, n: u32) {
        unsafe {
            gmp::mpz_fac_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes the double factorial of `n`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 8 * 6 * 4 * 2
    /// i.assign_factorial_2(10);
    /// assert!(i == 3840);
    /// ```
    pub fn assign_factorial_2(&mut self, n: u32) {
        unsafe {
            gmp::mpz_2fac_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes the `m`-multi factorial of `n`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 7 * 4 * 1
    /// i.assign_factorial_m(10, 3);
    /// assert!(i == 280);
    /// ```
    pub fn assign_factorial_m(&mut self, n: u32, m: u32) {
        unsafe {
            gmp::mpz_mfac_uiui(self.inner_mut(), n.into(), m.into());
        }
    }

    /// Computes the primorial of `n`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// // 7 * 5 * 3 * 2
    /// i.assign_primorial(10);
    /// assert!(i == 210);
    /// ```
    pub fn assign_primorial(&mut self, n: u32) {
        unsafe {
            gmp::mpz_primorial_ui(self.inner_mut(), n.into());
        }
    }

    math_op1! {
        /// Computes the binomial coefficient `self` over `k`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// // 7 choose 2 is 21
        /// let mut i = Integer::from(7);
        /// assert!(*i.binomial(2) == 21);
        /// ```
        fn binomial;
        /// Holds a computation of the binomial coefficient over `k`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugint::Integer;
        /// // 7 choose 2 is 21
        /// let i = Integer::from(7);
        /// assert!(Integer::from(i.binomial_hold(2)) == 21);
        /// ```
        fn binomial_hold -> BinomialHold;
        gmp::mpz_bin_ui,
        k: u32
    }

    /// Computes the binomial coefficient `n` over `k`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// // 7 choose 2 is 21
    /// let mut i = Integer::new();
    /// i.assign_binomial_u(7, 2);
    /// assert!(i == 21);
    /// ```
    pub fn assign_binomial_u(&mut self, n: u32, k: u32) {
        unsafe {
            gmp::mpz_bin_uiui(self.inner_mut(), n.into(), k.into());
        }
    }

    /// Computes the Fibonacci number.
    ///
    /// This function is meant for an isolated number. If a sequence
    /// of Fibonacci numbers is required, the first two values of the
    /// sequence should be computed with `assign_fibonacci_2()`, then
    /// iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_fibonacci(12);
    /// assert!(i == 144);
    /// ```
    pub fn assign_fibonacci(&mut self, n: u32) {
        unsafe {
            gmp::mpz_fib_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes a Fibonacci number, and the previous Fibonacci number.
    ///
    /// This function is meant to calculate isolated numbers. If a
    /// sequence of Fibonacci numbers is required, the first two
    /// values of the sequence should be computed with this function,
    /// then iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// let mut j = Integer::new();
    /// i.assign_fibonacci_2(&mut j, 12);
    /// assert!(i == 144);
    /// assert!(j == 89);
    /// // Fibonacci number F[-1] is 1
    /// i.assign_fibonacci_2(&mut j, 0);
    /// assert!(i == 0);
    /// assert!(j == 1);
    /// ```
    pub fn assign_fibonacci_2(&mut self, previous: &mut Integer, n: u32) {
        unsafe {
            gmp::mpz_fib2_ui(self.inner_mut(), previous.inner_mut(), n.into());
        }
    }

    /// Computes the Lucas number.
    ///
    /// This function is meant for an isolated number. If a sequence
    /// of Lucas numbers is required, the first two values of the
    /// sequence should be computed with `assign_lucas_2()`, then
    /// iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_lucas(12);
    /// assert!(i == 322);
    /// ```
    pub fn assign_lucas(&mut self, n: u32) {
        unsafe {
            gmp::mpz_lucnum_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes a Lucas number, and the previous Lucas number.
    ///
    /// This function is meant to calculate isolated numbers. If a
    /// sequence of Lucas numbers is required, the first two values of
    /// the sequence should be computed with this function, then
    /// iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// let mut j = Integer::new();
    /// i.assign_lucas_2(&mut j, 12);
    /// assert!(i == 322);
    /// assert!(j == 199);
    /// i.assign_lucas_2(&mut j, 0);
    /// assert!(i == 2);
    /// assert!(j == -1);
    /// ```
    pub fn assign_lucas_2(&mut self, previous: &mut Integer, n: u32) {
        unsafe {
            gmp::mpz_lucnum2_ui(self.inner_mut(),
                                previous.inner_mut(),
                                n.into());
        }
    }

    /// Compares the absolute values of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::cmp::Ordering;
    /// let a = Integer::from(-10);
    /// let b = Integer::from(4);
    /// assert!(a.cmp_abs(&b) == Ordering::Greater);
    /// ```
    pub fn cmp_abs(&self, other: &Integer) -> Ordering {
        unsafe { gmp::mpz_cmpabs(self.inner(), other.inner()).cmp(&0) }
    }

    /// Returns the same result as self.cmp(0), but is faster.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// use std::cmp::Ordering;
    /// assert!(Integer::from(-5).sign() == Ordering::Less);
    /// assert!(Integer::from(0).sign() == Ordering::Equal);
    /// assert!(Integer::from(5).sign() == Ordering::Greater);
    /// ```
    pub fn sign(&self) -> Ordering {
        unsafe { gmp::mpz_sgn(self.inner()).cmp(&0) }
    }

    /// Returns the number of bits required to represent the absolute
    /// value of `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    ///
    /// assert!(Integer::from(0).significant_bits() == 0);
    /// assert!(Integer::from(1).significant_bits() == 1);
    /// assert!(Integer::from(-1).significant_bits() == 1);
    /// assert!(Integer::from(4).significant_bits() == 3);
    /// assert!(Integer::from(-4).significant_bits() == 3);
    /// assert!(Integer::from(7).significant_bits() == 3);
    /// assert!(Integer::from(-7).significant_bits() == 3);
    /// ```
    pub fn significant_bits(&self) -> u32 {
        let bits = unsafe { gmp::mpz_sizeinbase(self.inner(), 2) };
        if bits > u32::MAX as usize {
            panic!("overflow");
        }
        // sizeinbase returns 1 if number is 0
        if bits == 1 && *self == 0 {
            0
        } else {
            bits as u32
        }
    }

    /// Returns the number of ones in `self` if the value >= 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(0).count_ones() == Some(0));
    /// assert!(Integer::from(15).count_ones() == Some(4));
    /// assert!(Integer::from(-1).count_ones() == None);
    /// ```
    pub fn count_ones(&self) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_popcount(self.inner()) })
    }

    /// Retuns the Hamming distance between `self` and `other` if they
    /// have the same sign.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(-1);
    /// assert!(Integer::from(0).ham_dist(&i) == None);
    /// assert!(Integer::from(-1).ham_dist(&i) == Some(0));
    /// assert!(Integer::from(-13).ham_dist(&i) == Some(2));
    /// ```
    pub fn ham_dist(&self, other: &Integer) -> Option<u32> {
        bitcount_to_u32(unsafe {
                            gmp::mpz_hamdist(self.inner(), other.inner())
                        })
    }

    /// Returns the location of the first zero, starting at `start`.
    /// If the bit at location `start` is zero, returns `start`.
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(-2).find_zero(0) == Some(0));
    /// assert!(Integer::from(-2).find_zero(1) == None);
    /// assert!(Integer::from(15).find_zero(0) == Some(4));
    /// assert!(Integer::from(15).find_zero(20) == Some(20));
    pub fn find_zero(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan0(self.inner(), start.into()) })
    }

    /// Returns the location of the first one, starting at `start`.
    /// If the bit at location `start` is one, returns `start`.
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(1).find_one(0) == Some(0));
    /// assert!(Integer::from(1).find_one(1) == None);
    /// assert!(Integer::from(-16).find_one(0) == Some(4));
    /// assert!(Integer::from(-16).find_one(20) == Some(20));
    pub fn find_one(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan1(self.inner(), start.into()) })
    }

    /// Sets the bit at location `index` to 1 if `val` is `true` or 0
    /// if `val` is `false`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::{Assign, Integer};
    /// let mut i = Integer::from(-1);
    /// assert!(*i.set_bit(0, false) == -2);
    /// i.assign(0xff);
    /// assert!(*i.set_bit(11, true) == 0x8ff);
    /// ```
    pub fn set_bit(&mut self, index: u32, val: bool) -> &mut Integer {
        unsafe {
            if val {
                gmp::mpz_setbit(self.inner_mut(), index.into());
            } else {
                gmp::mpz_clrbit(self.inner_mut(), index.into());
            }
        }
        self
    }

    /// Returns `true` if the bit at location `index` is 1 or `false`
    /// if the bit is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(0b100101);
    /// assert!(i.get_bit(0));
    /// assert!(!i.get_bit(1));
    /// assert!(i.get_bit(5));
    /// let neg = Integer::from(-1);
    /// assert!(neg.get_bit(1000));
    /// ```
    pub fn get_bit(&self, index: u32) -> bool {
        unsafe { gmp::mpz_tstbit(self.inner(), index.into()) != 0 }
    }

    /// Toggles the bit at location `index`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::from(0b100101);
    /// i.invert_bit(5);
    /// assert!(i == 0b101);
    /// ```
    pub fn invert_bit(&mut self, index: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_combit(self.inner_mut(), index.into());
        }
        self
    }

    #[cfg(feature = "random")]
    /// Generates a random number with a specified maximum number of
    /// bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugint;
    /// use rugint::Integer;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let mut i = Integer::new();
    ///     i.assign_random_bits(0, &mut rng);
    ///     assert!(i == 0);
    ///     i.assign_random_bits(80, &mut rng);
    ///     assert!(i.significant_bits() <= 80);
    /// }
    /// ```
    pub fn assign_random_bits<R: Rng>(&mut self, bits: u32, rng: &mut R) {
        self.assign(0);
        if bits == 0 {
            return;
        }
        let limb_bits = gmp::LIMB_BITS as u32;
        let whole_limbs = (bits / limb_bits) as usize;
        let extra_bits = bits % limb_bits;
        // Avoid conditions and overflow, equivalent to:
        // let total_limbs = whole_limbs + if extra_bits == 0 { 0 } else { 1 };
        let total_limbs = whole_limbs +
                          ((extra_bits + limb_bits - 1) / limb_bits) as usize;
        let limbs = unsafe {
            if (self.inner().alloc as usize) < total_limbs {
                gmp::_mpz_realloc(self.inner_mut(), total_limbs as c_long);
            }
            slice::from_raw_parts_mut(self.inner().d, total_limbs)
        };
        let mut limbs_used: c_int = 0;
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut val: gmp::limb_t = rng.gen();
            if i == whole_limbs {
                val &= ((1 as gmp::limb_t) << extra_bits) - 1;
            }
            if val != 0 {
                limbs_used = i as c_int + 1;
            }
            *limb = val;
        }
        unsafe {
            self.inner_mut().size = limbs_used;
        }
    }

    #[cfg(feature = "random")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugint;
    /// use rugint::Integer;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let mut random = Integer::from(15);
    ///     random.random_below(&mut rng);
    ///     println!("0 <= {} < 15", random);
    ///     assert!(random < 15);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    pub fn random_below<R: Rng>(&mut self, rng: &mut R) -> &mut Integer {
        assert_eq!(self.sign(), Ordering::Greater, "cannot be below zero");
        let bits = self.significant_bits();
        let limb_bits = gmp::LIMB_BITS as u32;
        let whole_limbs = (bits / limb_bits) as usize;
        let extra_bits = bits % limb_bits;
        // Avoid conditions and overflow, equivalent to:
        // let total_limbs = whole_limbs + if extra_bits == 0 { 0 } else { 1 };
        let total_limbs = whole_limbs +
                          ((extra_bits + limb_bits - 1) / limb_bits) as usize;
        let limbs =
            unsafe { slice::from_raw_parts_mut(self.inner().d, total_limbs) };
        // if the random number is >= bound, restart
        'restart: loop {
            let mut limbs_used: c_int = 0;
            let mut still_equal = true;
            'next_limb: for i in (0..total_limbs).rev() {
                let mut val: gmp::limb_t = rng.gen();
                if i == whole_limbs {
                    val &= ((1 as gmp::limb_t) << extra_bits) - 1;
                }
                if limbs_used == 0 && val != 0 {
                    limbs_used = i as c_int + 1;
                }
                if still_equal {
                    if val > limbs[i] {
                        continue 'restart;
                    }
                    if val == limbs[i] {
                        continue 'next_limb;
                    }
                    still_equal = false;
                }
                limbs[i] = val;
            }
            if !still_equal {
                unsafe {
                    self.inner_mut().size = limbs_used;
                }
                return self;
            }
        }
    }

    #[cfg(feature = "random")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugint;
    /// use rugint::Integer;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let bound = Integer::from(15);
    ///     let mut random = Integer::new();
    ///     random.assign_random_below(&bound, &mut rng);
    ///     println!("0 <= {} < {}", random, bound);
    ///     assert!(random < bound);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    pub fn assign_random_below<R: Rng>(&mut self,
                                       bound: &Integer,
                                       rng: &mut R) {
        self.assign(bound);
        self.random_below(rng);
    }
}

fn check_str_radix(src: &str, radix: i32) -> Result<&str, ParseIntegerError> {
    use self::ParseIntegerError as Error;
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
    for c in chars {
        let digit_value = match c {
            '0'...'9' => c as i32 - '0' as i32,
            'a'...'z' => c as i32 - 'a' as i32 + 10,
            'A'...'Z' => c as i32 - 'A' as i32 + 10,
            _ => return Err(Error { kind: Kind::InvalidDigit }),
        };
        if digit_value >= radix {
            return Err(Error { kind: Kind::InvalidDigit });
        }
        got_digit = true;
    }
    if !got_digit {
        return Err(Error { kind: Kind::NoDigits });
    }
    Ok(skip_plus)
}

impl FromStr for Integer {
    type Err = ParseIntegerError;
    fn from_str(src: &str) -> Result<Integer, ParseIntegerError> {
        let mut i = Integer::new();
        i.assign_str(src)?;
        Ok(i)
    }
}

macro_rules! from_borrow {
    { $T:ty } => {
        impl<'a> From<$T> for Integer {
            fn from(t: $T) -> Integer {
                let mut ret = Integer::new();
                ret.assign(t);
                ret
            }
        }
    };
}

impl Assign for Integer {
    fn assign(&mut self, mut other: Integer) {
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Integer> for Integer {
    fn assign(&mut self, other: &'a Integer) {
        unsafe {
            gmp::mpz_set(self.inner_mut(), other.inner());
        }
    }
}

impl<'a> From<&'a Integer> for Integer {
    fn from(val: &Integer) -> Integer {
        unsafe {
            let mut inner: mpz_t = mem::uninitialized();
            gmp::mpz_init_set(&mut inner, val.inner());
            Integer { inner: inner }
        }
    }
}

impl Assign<u32> for Integer {
    fn assign(&mut self, val: u32) {
        unsafe {
            xgmp::mpz_set_u32(self.inner_mut(), val);
        }
    }
}

impl From<u32> for Integer {
    fn from(val: u32) -> Integer {
        unsafe {
            let mut inner: mpz_t = mem::uninitialized();
            gmp::mpz_init_set_ui(&mut inner, val.into());
            Integer { inner: inner }
        }
    }
}

impl Assign<i32> for Integer {
    fn assign(&mut self, val: i32) {
        unsafe {
            xgmp::mpz_set_i32(self.inner_mut(), val);
        }
    }
}

impl From<i32> for Integer {
    fn from(val: i32) -> Integer {
        unsafe {
            let mut inner: mpz_t = mem::uninitialized();
            gmp::mpz_init_set_si(&mut inner, val.into());
            Integer { inner: inner }
        }
    }
}

impl Assign<u64> for Integer {
    fn assign(&mut self, val: u64) {
        unsafe {
            xgmp::mpz_set_u64(self.inner_mut(), val);
        }
    }
}

impl From<u64> for Integer {
    fn from(val: u64) -> Integer {
        if mem::size_of::<c_ulong>() >= 8 {
            unsafe {
                let mut inner: mpz_t = mem::uninitialized();
                gmp::mpz_init_set_ui(&mut inner, val as c_ulong);
                Integer { inner: inner }
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

impl Assign<i64> for Integer {
    fn assign(&mut self, val: i64) {
        unsafe {
            xgmp::mpz_set_i64(self.inner_mut(), val);
        }
    }
}

impl From<i64> for Integer {
    fn from(val: i64) -> Integer {
        if mem::size_of::<c_long>() >= 8 {
            unsafe {
                let mut inner: mpz_t = mem::uninitialized();
                gmp::mpz_init_set_si(&mut inner, val as c_long);
                Integer { inner: inner }
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

macro_rules! arith_unary {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        impl $Imp for Integer {
            type Output = Integer;
            fn $method(mut self) -> Integer {
                self.$method_assign();
                self
            }
        }

        impl $ImpAssign for Integer {
            fn $method_assign(&mut self) {
                unsafe {
                    $func(self.inner_mut(), self.inner());
                }
            }
        }

        impl<'a> $Imp for &'a Integer {
            type Output = $Hold<'a>;
            fn $method(self) -> $Hold<'a> {
                $Hold { op: self }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            op: &'a Integer,
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(), rhs.op.inner());
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        impl<'a> $Imp<&'a Integer> for Integer {
            type Output = Integer;
            fn $method(mut self, op: &'a Integer) -> Integer {
                $ImpAssign::<&'a Integer>::$method_assign(&mut self, op);
                self
            }
        }

        impl $Imp<Integer> for Integer {
            type Output = Integer;
            fn $method(self, op: Integer) -> Integer {
                self.$method(&op)
            }
        }

        impl<'a> $ImpAssign<&'a Integer> for Integer {
            fn $method_assign(&mut self, op: &'a Integer) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), op.inner());
                }
            }
        }

        impl $ImpAssign<Integer> for Integer {
            fn $method_assign(&mut self, op: Integer) {
                self.$method_assign(&op);
            }
        }

        impl<'a> $Imp<&'a Integer> for &'a Integer {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Integer) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            lhs: &'a Integer,
            rhs: &'a Integer,
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.inner());
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

macro_rules! arith_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! { $Imp $method,
                         $ImpAssign $method_assign,
                         $func,
                         $Hold }

        impl<'a> $ImpFromAssign<&'a Integer> for Integer {
            fn $method_from_assign(&mut self, lhs: &'a Integer) {
                unsafe {
                    $func(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }

        impl $ImpFromAssign<Integer> for Integer {
            fn $method_from_assign(&mut self, lhs: Integer) {
                self.$method_from_assign(&lhs);
            }
        }

    };
}

arith_unary! { Neg neg, NegAssign neg_assign, gmp::mpz_neg, NegHold }
arith_binary! { Add add, AddAssign add_assign, gmp::mpz_add, AddHold }
arith_noncommut! {
    Sub sub,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    gmp::mpz_sub,
    SubHold
}
arith_binary! { Mul mul, MulAssign mul_assign, gmp::mpz_mul, MulHold }
arith_noncommut! {
    Div div,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    xgmp::mpz_tdiv_q_check_0,
    DivHold
}
arith_noncommut! {
    Rem rem,
    RemAssign rem_assign,
    RemFromAssign rem_from_assign,
    xgmp::mpz_tdiv_r_check_0,
    RemHold
}
arith_unary! { Not not, NotAssign not_assign, gmp::mpz_com, NotHold }
arith_binary! {
    BitAnd bitand, BitAndAssign bitand_assign, gmp::mpz_and, BitAndHold
}
arith_binary! {
    BitOr bitor, BitOrAssign bitor_assign, gmp::mpz_ior, BitOrHold
}
arith_binary! {
    BitXor bitxor, BitXorAssign bitxor_assign, gmp::mpz_xor, BitXorHold
}

macro_rules! arith_prim {
    ($Imp:ident $method:ident,
     $ImpAssign:ident $method_assign:ident,
     $T:ty,
     $func:path,
     $Hold:ident) => {
        impl $Imp<$T> for Integer {
            type Output = Integer;
            fn $method(mut self, op: $T) -> Integer {
                self.$method_assign(op);
                self
            }
        }

        impl $ImpAssign<$T> for Integer {
            fn $method_assign(&mut self, op: $T) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), op.into());
                }
            }
        }

        impl<'a> $Imp<$T> for &'a Integer {
            type Output = $Hold<'a>;
            fn $method(self, op: $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: op,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            lhs: &'a Integer,
            rhs: $T,
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.into());
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

macro_rules! arith_prim_noncommut {
    ($Imp:ident $method:ident,
     $ImpAssign:ident $method_assign:ident,
     $ImpFromAssign:ident $method_from_assign:ident,
     $T:ty,
     $func:path,
     $func_from:path,
     $Hold:ident,
     $HoldFrom:ident) => {
        arith_prim! {
            $Imp $method,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Integer> for $T {
            type Output = Integer;
            fn $method(self, mut op: Integer) -> Integer {
                op.$method_from_assign(self);
                op
            }
        }

        impl $ImpFromAssign<$T> for Integer {
            fn $method_from_assign(&mut self, lhs: $T) {
                unsafe {
                    $func_from(self.inner_mut(), lhs.into(), self.inner());
                }
            }
        }

        impl<'a> $Imp<&'a Integer> for $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, op: &'a Integer) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: self,
                    rhs: op,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $HoldFrom<'a> {
            lhs: $T,
            rhs: &'a Integer,
        }


        impl<'a> Assign<$HoldFrom<'a>> for Integer {
            fn assign(&mut self, rhs: $HoldFrom) {
                unsafe {
                    $func_from(self.inner_mut(),
                               rhs.lhs.into(),
                               rhs.rhs.inner());
                }
            }
        }

        from_borrow! { $HoldFrom<'a> }
    };
}

macro_rules! arith_prim_commut {
    ($Imp:ident $method:ident,
     $ImpAssign:ident $method_assign:ident,
     $T:ty,
     $func:path,
     $Hold:ident) => {
        arith_prim! {
            $Imp $method,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Integer> for $T {
            type Output = Integer;
            fn $method(self, op: Integer) -> Integer {
                op.$method(self)
            }
        }

        impl<'a> $Imp<&'a Integer> for $T {
            type Output = $Hold<'a>;
            fn $method(self, op: &'a Integer) -> $Hold<'a> {
                op.$method(self)
            }
        }
    };
}

arith_prim_commut! {
    Add add, AddAssign add_assign, u32, gmp::mpz_add_ui, AddHoldU32
}
arith_prim_noncommut! {
    Sub sub,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    u32,
    gmp::mpz_sub_ui,
    gmp::mpz_ui_sub,
    SubHoldU32,
    SubFromHoldU32
}
arith_prim_commut! {
    Mul mul, MulAssign mul_assign, u32, gmp::mpz_mul_ui, MulHoldU32
}
arith_prim_noncommut! {
    Div div,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    u32,
    xgmp::mpz_tdiv_q_ui_check_0,
    xgmp::mpz_ui_tdiv_q_check_0,
    DivHoldU32,
    DivFromHoldU32
}
arith_prim_noncommut! {
    Rem rem,
    RemAssign rem_assign,
    RemFromAssign rem_from_assign,
    u32,
    xgmp::mpz_tdiv_r_ui_check_0,
    xgmp::mpz_ui_tdiv_r_check_0,
    RemHoldU32,
    RemFromHoldU32
}
arith_prim! {
    Shl shl, ShlAssign shl_assign, u32, gmp::mpz_mul_2exp, ShlHoldU32
}
arith_prim! {
    Shr shr, ShrAssign shr_assign, u32, gmp::mpz_fdiv_q_2exp, ShrHoldU32
}
arith_prim! { Pow pow, PowAssign pow_assign, u32, gmp::mpz_pow_ui, PowHoldU32 }
arith_prim_commut! {
    BitAnd bitand,
    BitAndAssign bitand_assign,
    u32,
    xgmp::bitand_ui,
    BitAndHoldU32
}
arith_prim_commut! {
    BitOr bitor, BitOrAssign bitor_assign, u32, xgmp::bitor_ui, BitOrHoldU32
}
arith_prim_commut! {
    BitXor bitxor,
    BitXorAssign bitxor_assign,
    u32,
    xgmp::bitxor_ui,
    BitXorHoldU32
}

arith_prim_commut! {
    Add add, AddAssign add_assign, i32, xgmp::mpz_add_si, AddHoldI32
}
arith_prim_noncommut! {
    Sub sub,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    i32,
    xgmp::mpz_sub_si,
    xgmp::mpz_si_sub,
    SubHoldI32,
    SubFromHoldI32
}
arith_prim_commut! {
    Mul mul, MulAssign mul_assign, i32, gmp::mpz_mul_si, MulHoldI32
}
arith_prim_noncommut! {
    Div div,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    i32,
    xgmp::mpz_tdiv_q_si_check_0,
    xgmp::mpz_si_tdiv_q_check_0,
    DivHoldI32,
    DivFromHoldI32
}
arith_prim_noncommut! {
    Rem rem,
    RemAssign rem_assign,
    RemFromAssign rem_from_assign,
    i32,
    xgmp::mpz_tdiv_r_si_check_0,
    xgmp::mpz_si_tdiv_r_check_0,
    RemHoldI32,
    RemFromHoldI32
}
arith_prim! {
    Shl shl, ShlAssign shl_assign, i32, xgmp::mpz_lshift_si, ShlHoldI32
}
arith_prim! {
    Shr shr, ShrAssign shr_assign, i32, xgmp::mpz_rshift_si, ShrHoldI32
}
arith_prim_commut! {
    BitAnd bitand,
    BitAndAssign bitand_assign,
    i32,
    xgmp::bitand_si,
    BitAndHoldI32
}
arith_prim_commut! {
    BitOr bitor, BitOrAssign bitor_assign, i32, xgmp::bitor_si, BitOrHoldI32
}
arith_prim_commut! {
    BitXor bitxor,
    BitXorAssign bitxor_assign,
    i32,
    xgmp::bitxor_si,
    BitXorHoldI32
}

macro_rules! op_mul {
    {
        $(#[$attr:meta])* impl $Imp:ident $method:ident;
        $(#[$attr_assign:meta])* impl $ImpAssign:ident $method_assign:ident;
        $Hold:ident, $rhs_method:ident, $func:path
    } => {
        impl<'a> $Imp<$Hold<'a>> for Integer {
            type Output = Integer;
            $(#[$attr])*
            fn $method(mut self, rhs: $Hold) -> Integer {
                self.$method_assign(rhs);
                self
            }
        }

        impl<'a> $ImpAssign<$Hold<'a>> for Integer  {
            $(#[$attr_assign])*
            fn $method_assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(),
                          rhs.lhs.inner(), rhs.rhs.$rhs_method());
                }
            }
        }
    };
}

op_mul! {
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let init = Integer::from(100);
    /// let acc = init + &m1 * &m2;
    /// assert!(acc == 121);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let mut acc = Integer::from(100);
    /// acc += &m1 * &m2;
    /// assert!(acc == 121);
    /// ```
    impl AddAssign add_assign;
    MulHold, inner, gmp::mpz_addmul
}

op_mul! {
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init + &m * 7u32;
    /// assert!(acc == 121);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc += &m * 7u32;
    /// assert!(acc == 121);
    /// ```
    impl AddAssign add_assign;
    MulHoldU32, into, gmp::mpz_addmul_ui
}

op_mul! {
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init + &m * -7i32;
    /// assert!(acc == 79);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc += &m * -7i32;
    /// assert!(acc == 79);
    /// ```
    impl AddAssign add_assign;
    MulHoldI32, into, xgmp::mpz_addmul_si
}


op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let init = Integer::from(100);
    /// let acc = init - &m1 * &m2;
    /// assert!(acc == 79);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let mut acc = Integer::from(100);
    /// acc -= &m1 * &m2;
    /// assert!(acc == 79);
    /// ```
    impl SubAssign sub_assign;
    MulHold, inner, gmp::mpz_submul
}

op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init - &m * 7u32;
    /// assert!(acc == 79);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc -= &m * 7u32;
    /// assert!(acc == 79);
    /// ```
    impl SubAssign sub_assign;
    MulHoldU32, into, gmp::mpz_submul_ui
}

op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init - &m * -7i32;
    /// assert!(acc == 121);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc -= &m * -7i32;
    /// assert!(acc == 121);
    /// ```
    impl SubAssign sub_assign;
    MulHoldI32, into, xgmp::mpz_submul_si
}

impl Eq for Integer {}

impl Ord for Integer {
    fn cmp(&self, other: &Integer) -> Ordering {
        let ord = unsafe { gmp::mpz_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Integer) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<f64> for Integer {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if other.is_nan() {
            None
        } else {
            let ord = unsafe { gmp::mpz_cmp_d(self.inner(), *other) };
            Some(ord.cmp(&0))
        }
    }
}

impl PartialEq<f64> for Integer {
    fn eq(&self, other: &f64) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd<Integer> for f64 {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        match other.partial_cmp(self) {
            None => None,
            Some(x) => Some(x.reverse()),
        }
    }
}

impl PartialEq<Integer> for f64 {
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<f32> for Integer {
    fn partial_cmp(&self, other: &f32) -> Option<Ordering> {
        let o = *other as f64;
        self.partial_cmp(&o)
    }
}

impl PartialEq<f32> for Integer {
    fn eq(&self, other: &f32) -> bool {
        let o = *other as f64;
        self.eq(&o)
    }
}

impl PartialEq<Integer> for f32 {
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<Integer> for f32 {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        match other.partial_cmp(self) {
            None => None,
            Some(x) => Some(x.reverse()),
        }
    }
}

macro_rules! cmp {
    { $T:ty, $func:path } => {
        impl PartialOrd<$T> for Integer {
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                let ord = unsafe { $func(self.inner(), (*other).into()) };
                Some(ord.cmp(&0))
            }
        }

        impl PartialEq<$T> for Integer {
            fn eq(&self, other: &$T) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<Integer> for $T {
            fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
                match other.partial_cmp(self) {
                    Some(x) => Some(x.reverse()),
                    None => None,
                }
            }
        }

        impl PartialEq<Integer> for $T {
            fn eq(&self, other: &Integer) -> bool {
                other.eq(self)
            }
        }
    };
}

cmp! { u32, xgmp::mpz_cmp_u32 }
cmp! { i32, xgmp::mpz_cmp_i32 }
cmp! { u64, xgmp::mpz_cmp_u64 }
cmp! { i64, xgmp::mpz_cmp_i64 }

fn make_string(i: &Integer, radix: i32, to_upper: bool) -> String {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let i_size = unsafe { gmp::mpz_sizeinbase(i.inner(), radix) };
    // size + 2 for '-' and nul
    let size = i_size.checked_add(2).unwrap();
    let mut buf = Vec::<u8>::with_capacity(size);
    let case_radix = if to_upper { -radix } else { radix };
    unsafe {
        buf.set_len(size);
        gmp::mpz_get_str(buf.as_mut_ptr() as *mut c_char,
                         case_radix as c_int,
                         i.inner());
        let nul_index = buf.iter().position(|&x| x == 0).unwrap();
        buf.set_len(nul_index);
        String::from_utf8_unchecked(buf)
    }
}

fn fmt_radix(i: &Integer,
             f: &mut Formatter,
             radix: i32,
             to_upper: bool,
             prefix: &str)
             -> fmt::Result {
    let s = make_string(i, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

impl Display for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// An error which can be returned when parsing an `Integer`.
pub struct ParseIntegerError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    InvalidDigit,
    NoDigits,
}

impl Error for ParseIntegerError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidDigit => "invalid digit found in string",
            NoDigits => "string has no digits",
        }
    }
}

impl Display for ParseIntegerError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

fn bitcount_to_u32(bits: gmp::bitcnt_t) -> Option<u32> {
    let max: gmp::bitcnt_t = !0;
    if bits == max {
        None
    } else if bits > u32::MAX as gmp::bitcnt_t {
        panic!("overflow")
    } else {
        Some(bits as u32)
    }
}

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Integer {
    type Output = mpz_t;
    fn inner(&self) -> &mpz_t {
        &self.inner
    }
}

impl InnerMut for Integer {
    unsafe fn inner_mut(&mut self) -> &mut mpz_t {
        &mut self.inner
    }
}

macro_rules! hold_math_op1 {
    {
        $(#[$attr_hold:meta])* struct $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            val: &'a Integer,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(self.inner_mut(),
                          src.val.inner() $(, src.$param.into())*);
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

macro_rules! hold_math_op1_2 {
    {
        $(#[$attr_hold:meta])* struct $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            val: &'a Integer,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for (&'a mut Integer, &'a mut Integer) {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(self.0.inner_mut(), self.1.inner_mut(),
                          src.val.inner() $(, src.$param.into())*);
                }
            }
        }
    };
}

macro_rules! hold_math_op2 {
    {
        $(#[$attr_hold:meta])* struct $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            lhs: &'a Integer,
            rhs: &'a Integer,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(self.inner_mut(), src.lhs.inner(),
                          src.rhs.inner() $(, src.$param.into())*);
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

macro_rules! hold_math_op2_2 {
    {
        $(#[$attr_hold:meta])* struct $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            lhs: &'a Integer,
            rhs: &'a Integer,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for (&'a mut Integer, &'a mut Integer) {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(self.0.inner_mut(), self.1.inner_mut(),
                          src.lhs.inner(),
                          src.rhs.inner() $(, src.$param.into())*);
                }
            }
        }
    };
}

macro_rules! hold_math_op3 {
    {
        $(#[$attr_hold:meta])* struct $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            op1: &'a Integer,
            op2: &'a Integer,
            op3: &'a Integer,
            $($param: $T,)*
        }

        impl<'a> Assign<$Hold<'a>> for Integer {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(self.inner_mut(), src.op1.inner(), src.op2.inner(),
                          src.op3.inner() $(, src.$param.into())*);
                }
            }
        }

        from_borrow! { $Hold<'a> }
    };
}

hold_math_op2_2! { struct DivRemHold; xgmp::mpz_tdiv_qr_check_0 }
hold_math_op1! { struct AbsHold; gmp::mpz_abs }
hold_math_op2! { struct DivExactHold; xgmp::mpz_divexact_check_0 }
hold_math_op1! {
    struct DivExactUHold; xgmp::mpz_divexact_ui_check_0, divisor: u32
}
hold_math_op3! { struct PowModHold; xgmp::mpz_powm_check_inverse }
hold_math_op1! { struct RootHold; gmp::mpz_root, n: u32 }
hold_math_op1_2! { struct RootRemHold; gmp::mpz_rootrem, n: u32 }
hold_math_op1! { struct SqrtHold; gmp::mpz_sqrt }
hold_math_op1_2! { struct SqrtRemHold; gmp::mpz_sqrtrem }
hold_math_op2! { struct GcdHold; gmp::mpz_gcd }
hold_math_op2! { struct LcmHold; gmp::mpz_lcm }

#[derive(Clone, Copy)]
pub struct InvertHold<'a> {
    lhs: &'a Integer,
    rhs: &'a Integer,
}

impl<'a> Assign<InvertHold<'a>> for (&'a mut Integer, &'a mut bool) {
    fn assign(&mut self, src: InvertHold<'a>) {
        *self.1 = unsafe {
            xgmp::mpz_invert_check_0(self.0.inner_mut(),
                                     src.lhs.inner(),
                                     src.rhs.inner())
        } != 0;
    }
}

#[derive(Clone, Copy)]
pub struct RemoveFactorHold<'a> {
    lhs: &'a Integer,
    rhs: &'a Integer,
}

impl<'a> Assign<RemoveFactorHold<'a>> for (&'a mut Integer, &'a mut u32) {
    fn assign(&mut self, src: RemoveFactorHold<'a>) {
        let cnt = unsafe {
            gmp::mpz_remove(self.0.inner_mut(),
                            src.lhs.inner(),
                            src.rhs.inner())
        };
        assert!(cnt as u32 as gmp::bitcnt_t == cnt, "overflow");
        *self.1 = cnt as u32;
    }
}

hold_math_op1! { struct BinomialHold; gmp::mpz_bin_ui, k: u32 }

/// A small integer that does not require any memory allocation.
///
/// This can be useful when you have a `u64`, `i64`, `u32` or `i32`
/// but need a reference to an `Integer`.
///
/// If there are functions that take a `u32` or `i32` directly instead
/// of an `Integer` reference, using them can still be faster than
/// using a `SmallInteger`; the functions would still need to check
/// for the size of an `Integer` obtained using `SmallInteger`.
///
/// # Examples
///
/// ```rust
/// use rugint::{Integer, SmallInteger};
/// // `a` requires a heap allocation
/// let mut a = Integer::from(250);
/// // `b` can reside on the stack
/// let mut b = SmallInteger::from(-100);
/// a.lcm(b.get());
/// assert!(a == 500);
/// // another computation:
/// a.lcm(SmallInteger::from(30).get());
/// assert!(a == 1500);
/// ```
#[derive(Clone, Copy)]
#[repr(C)]
pub struct SmallInteger {
    inner: mpz_t,
    limb: [gmp::limb_t; LIMBS_IN_SMALL_INTEGER],
}

const LIMBS_IN_SMALL_INTEGER: usize = 64 / gmp::LIMB_BITS as usize;

impl SmallInteger {
    /// Creates a `SmallInteger` with value 0.
    pub fn new() -> SmallInteger {
        SmallInteger {
            inner: mpz_t {
                size: 0,
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
                d: ptr::null_mut(),
            },
            limb: [0; LIMBS_IN_SMALL_INTEGER],
        }
    }

    /// Borrows the `SmallInteger` as an `Integer`.
    pub fn get(&mut self) -> &Integer {
        self.inner.d = &mut self.limb[0];
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<T> From<T> for SmallInteger
    where SmallInteger: Assign<T>
{
    fn from(val: T) -> SmallInteger {
        let mut ret = SmallInteger::new();
        ret.assign(val);
        ret
    }
}

impl Assign<u32> for SmallInteger {
    fn assign(&mut self, val: u32) {
        if val == 0 {
            self.inner.size = 0;
        } else {
            self.inner.size = 1;
            self.limb[0] = val as gmp::limb_t;
        }
    }
}

impl Assign<i32> for SmallInteger {
    fn assign(&mut self, val: i32) {
        self.assign(val.wrapping_abs() as u32);
        if val < 0 {
            self.inner.size = -self.inner.size;
        }
    }
}

impl Assign<u64> for SmallInteger {
    fn assign(&mut self, val: u64) {
        match gmp::LIMB_BITS {
            64 => {
                if val == 0 {
                    self.inner.size = 0;
                } else {
                    self.inner.size = 1;
                    self.limb[0] = val as gmp::limb_t;
                }
            }
            32 => {
                if val == 0 {
                    self.inner.size = 0;
                } else if val <= 0xffff_ffff {
                    self.inner.size = 1;
                    self.limb[0] = val as u32 as gmp::limb_t;
                } else {
                    self.inner.size = 2;
                    self.limb[0] = val as u32 as gmp::limb_t;
                    self.limb[1 + 0] = (val >> 32) as u32 as gmp::limb_t;
                }
            }
            _ => {
                unreachable!();
            }
        }
    }
}

impl Assign<i64> for SmallInteger {
    fn assign(&mut self, val: i64) {
        self.assign(val.wrapping_abs() as u64);
        if val < 0 {
            self.inner.size = -self.inner.size;
        }
    }
}

#[cfg(test)]
mod tests {
    use gmp_mpfr_sys::gmp;
    use integer::*;
    use std::{f32, f64, i32, i64, u32, u64};
    use std::cmp::Ordering;
    use std::mem;

    #[test]
    fn check_arith_u_s() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u32::MAX];
        let s = [i32::MIN, -101, -100, -1, 0, 1, 100, 101, i32::MAX];
        for &op in &u {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                assert!(b.clone() + op == b.clone() + &iop);
                assert!(b.clone() - op == b.clone() - &iop);
                assert!(b.clone() * op == b.clone() * &iop);
                if op != 0 {
                    assert!(b.clone() / op == b.clone() / &iop);
                    assert!(b.clone() % op == b.clone() % &iop);
                }
                assert!(b.clone() & op == b.clone() & &iop);
                assert!(b.clone() | op == b.clone() | &iop);
                assert!(b.clone() ^ op == b.clone() ^ &iop);
                assert!(op + b.clone() == iop.clone() + &b);
                assert!(op - b.clone() == iop.clone() - &b);
                assert!(op * b.clone() == iop.clone() * &b);
                if b.sign() != Ordering::Equal {
                    assert!(op / b.clone() == iop.clone() / &b);
                    assert!(op % b.clone() == iop.clone() % &b);
                }
                assert!(op & b.clone() == iop.clone() & &b);
                assert!(op | b.clone() == iop.clone() | &b);
                assert!(op ^ b.clone() == iop.clone() ^ &b);
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                assert!(b.clone() + op == b.clone() + &iop);
                assert!(b.clone() - op == b.clone() - &iop);
                assert!(b.clone() * op == b.clone() * &iop);
                if op != 0 {
                    assert!(b.clone() / op == b.clone() / &iop);
                    assert!(b.clone() % op == b.clone() % &iop);
                }
                assert!(b.clone() & op == b.clone() & &iop);
                assert!(b.clone() | op == b.clone() | &iop);
                assert!(b.clone() ^ op == b.clone() ^ &iop);
                assert!(op + b.clone() == iop.clone() + &b);
                assert!(op - b.clone() == iop.clone() - &b);
                assert!(op * b.clone() == iop.clone() * &b);
                if b.sign() != Ordering::Equal {
                    assert!(op / b.clone() == iop.clone() / &b);
                    assert!(op % b.clone() == iop.clone() % &b);
                }
                assert!(op & b.clone() == iop.clone() & &b);
                assert!(op | b.clone() == iop.clone() | &b);
                assert!(op ^ b.clone() == iop.clone() ^ &b);
            }
        }
    }

    #[test]
    fn check_ref_op() {
        let lhs = Integer::from(0x00ff);
        let rhs = Integer::from(0x0f0f);
        let pu = 30_u32;
        let pi = -15_i32;
        assert!(Integer::from(-&lhs) == -lhs.clone());
        assert!(Integer::from(&lhs + &rhs) == lhs.clone() + &rhs);
        assert!(Integer::from(&lhs - &rhs) == lhs.clone() - &rhs);
        assert!(Integer::from(&lhs * &rhs) == lhs.clone() * &rhs);
        assert!(Integer::from(&lhs / &rhs) == lhs.clone() / &rhs);
        assert!(Integer::from(&lhs % &rhs) == lhs.clone() % &rhs);
        assert!(Integer::from(!&lhs) == !lhs.clone());
        assert!(Integer::from(&lhs & &rhs) == lhs.clone() & &rhs);
        assert!(Integer::from(&lhs | &rhs) == lhs.clone() | &rhs);
        assert!(Integer::from(&lhs ^ &rhs) == lhs.clone() ^ &rhs);

        assert!(Integer::from(&lhs + pu) == lhs.clone() + pu);
        assert!(Integer::from(&lhs - pu) == lhs.clone() - pu);
        assert!(Integer::from(&lhs * pu) == lhs.clone() * pu);
        assert!(Integer::from(&lhs / pu) == lhs.clone() / pu);
        assert!(Integer::from(&lhs % pu) == lhs.clone() % pu);
        assert!(Integer::from(&lhs & pu) == lhs.clone() & pu);
        assert!(Integer::from(&lhs | pu) == lhs.clone() | pu);
        assert!(Integer::from(&lhs ^ pu) == lhs.clone() ^ pu);
        assert!(Integer::from(&lhs << pu) == lhs.clone() << pu);
        assert!(Integer::from(&lhs >> pu) == lhs.clone() >> pu);
        assert!(Integer::from((&lhs).pow(pu)) == lhs.clone().pow(pu));

        assert!(Integer::from(&lhs + pi) == lhs.clone() + pi);
        assert!(Integer::from(&lhs - pi) == lhs.clone() - pi);
        assert!(Integer::from(&lhs * pi) == lhs.clone() * pi);
        assert!(Integer::from(&lhs / pi) == lhs.clone() / pi);
        assert!(Integer::from(&lhs % pi) == lhs.clone() % pi);
        assert!(Integer::from(&lhs & pi) == lhs.clone() & pi);
        assert!(Integer::from(&lhs | pi) == lhs.clone() | pi);
        assert!(Integer::from(&lhs ^ pi) == lhs.clone() ^ pi);
        assert!(Integer::from(&lhs << pi) == lhs.clone() << pi);
        assert!(Integer::from(&lhs >> pi) == lhs.clone() >> pi);

        assert!(Integer::from(pu + &lhs) == pu + lhs.clone());
        assert!(Integer::from(pu - &lhs) == pu - lhs.clone());
        assert!(Integer::from(pu * &lhs) == pu * lhs.clone());
        assert!(Integer::from(pu / &lhs) == pu / lhs.clone());
        assert!(Integer::from(pu % &lhs) == pu % lhs.clone());
        assert!(Integer::from(pu & &lhs) == pu & lhs.clone());
        assert!(Integer::from(pu | &lhs) == pu | lhs.clone());
        assert!(Integer::from(pu ^ &lhs) == pu ^ lhs.clone());

        assert!(Integer::from(pi + &lhs) == pi + lhs.clone());
        assert!(Integer::from(pi - &lhs) == pi - lhs.clone());
        assert!(Integer::from(pi * &lhs) == pi * lhs.clone());
        assert!(Integer::from(pi / &lhs) == pi / lhs.clone());
        assert!(Integer::from(pi % &lhs) == pi % lhs.clone());
        assert!(Integer::from(pi & &lhs) == pi & lhs.clone());
        assert!(Integer::from(pi | &lhs) == pi | lhs.clone());
        assert!(Integer::from(pi ^ &lhs) == pi ^ lhs.clone());
    }

    #[test]
    fn check_shift_u_s() {
        let pos: Integer = Integer::from(11) << 100;
        let neg: Integer = Integer::from(-33) << 50;
        assert!(pos.clone() << 10 == pos.clone() >> -10);
        assert!(pos.clone() << 10 == Integer::from(11) << 110);
        assert!(pos.clone() << -100 == pos.clone() >> 100);
        assert!(pos.clone() << -100 == 11);
        assert!(neg.clone() << 10 == neg.clone() >> -10);
        assert!(neg.clone() << 10 == Integer::from(-33) << 60);
        assert!(neg.clone() << -100 == neg.clone() >> 100);
        assert!(neg.clone() << -100 == -1);
    }

    #[test]
    fn check_int_conversions() {
        let mut i = Integer::from(-1);
        assert!(i.to_u32_wrapping() == u32::MAX);
        assert!(i.to_i32_wrapping() == -1);
        i.assign(0xff000000u32);
        i <<= 4;
        assert!(i.to_u32_wrapping() == 0xf0000000u32);
        assert!(i.to_i32_wrapping() == 0xf0000000u32 as i32);
        i = i.clone() << 32 | i;
        assert!(i.to_u32_wrapping() == 0xf0000000u32);
        assert!(i.to_i32_wrapping() == 0xf0000000u32 as i32);
        i.neg_assign();
        assert!(i.to_u32_wrapping() == 0x10000000u32);
        assert!(i.to_i32_wrapping() == 0x10000000i32);
    }

    #[test]
    fn check_option_conversion() {
        let mut i = Integer::new();
        assert!(i.to_u32() == Some(0));
        assert!(i.to_i32() == Some(0));
        assert!(i.to_u64() == Some(0));
        assert!(i.to_i64() == Some(0));
        i -= 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == Some(-1));
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == Some(-1));

        i.assign(i32::MIN);
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == Some(i32::MIN));
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == Some(i32::MIN as i64));
        i -= 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == Some(i32::MIN as i64 - 1));
        i.assign(i32::MAX);
        assert!(i.to_u32() == Some(i32::MAX as u32));
        assert!(i.to_i32() == Some(i32::MAX));
        assert!(i.to_u64() == Some(i32::MAX as u64));
        assert!(i.to_i64() == Some(i32::MAX as i64));
        i += 1;
        assert!(i.to_u32() == Some(i32::MAX as u32 + 1));
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(i32::MAX as u64 + 1));
        assert!(i.to_i64() == Some(i32::MAX as i64 + 1));
        i.assign(u32::MAX);
        assert!(i.to_u32() == Some(u32::MAX));
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(u32::MAX as u64));
        assert!(i.to_i64() == Some(u32::MAX as i64));
        i += 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(u32::MAX as u64 + 1));
        assert!(i.to_i64() == Some(u32::MAX as i64 + 1));

        i.assign(i64::MIN);
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == Some(i64::MIN));
        i -= 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == None);
        i.assign(i64::MAX);
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(i64::MAX as u64));
        assert!(i.to_i64() == Some(i64::MAX));
        i += 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(i64::MAX as u64 + 1));
        assert!(i.to_i64() == None);
        i.assign(u64::MAX);
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == Some(u64::MAX));
        assert!(i.to_i64() == None);
        i += 1;
        assert!(i.to_u32() == None);
        assert!(i.to_i32() == None);
        assert!(i.to_u64() == None);
        assert!(i.to_i64() == None);
    }

    #[test]
    fn check_float_conversions() {
        let mut i = Integer::from(0);
        assert!(i.to_f32() == 0.0);
        assert!(i.to_f64() == 0.0);
        i.assign(0xff);
        assert!(i.to_f32() == 255.0);
        assert!(i.to_f64() == 255.0);
        i <<= 80;
        assert!(i.to_f32() == 255.0 * 2f32.powi(80));
        assert!(i.to_f64() == 255.0 * 2f64.powi(80));
        i = i.clone() << 30 | i;
        assert!(i.to_f32() == 255.0 * 2f32.powi(110));
        assert!(i.to_f64() == 255.0 * (2f64.powi(80) + 2f64.powi(110)));
        i <<= 100;
        assert!(i.to_f32() == f32::INFINITY);
        assert!(i.to_f64() == 255.0 * (2f64.powi(180) + 2f64.powi(210)));
        i <<= 1000;
        assert!(i.to_f32() == f32::INFINITY);
        assert!(i.to_f64() == f64::INFINITY);
        i.assign(-0xff_ffff);
        assert!(i.to_f32() == -0xff_ffff as f32);
        assert!(i.to_f64() == -0xff_ffff as f64);
        i.assign(-0xfff_ffff);
        println!("{:x}", (-i.to_f32()) as u32);
        assert!(i.to_f32() == -0xff_ffff0 as f32);
        assert!(i.to_f64() == -0xff_fffff as f64);
    }

    #[test]
    fn check_from_str() {
        let mut i: Integer = "+134".parse().unwrap();
        assert!(i == 134);
        i.assign_str_radix("-ffFFffffFfFfffffffffffffffffffff", 16)
            .unwrap();
        assert!(i.significant_bits() == 128);
        i -= 1;
        assert!(i.significant_bits() == 129);

        let bad_strings = [(" 1", None),
                           ("+-3", None),
                           ("-+3", None),
                           ("++3", None),
                           ("--3", None),
                           ("0+3", None),
                           ("0 ", None),
                           ("", None),
                           ("80", Some(8)),
                           ("0xf", Some(16)),
                           ("9", Some(9))];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Integer::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings = [("0", 10, 0),
                            ("+0", 16, 0),
                            ("-0", 2, 0),
                            ("99", 10, 99),
                            ("+Cc", 16, 0xcc),
                            ("-77", 8, -0o77)];
        for &(s, radix, i) in good_strings.into_iter() {
            assert!(Integer::from_str_radix(s, radix).unwrap() == i);
        }
    }

    #[test]
    fn check_formatting() {
        let i = Integer::from((-11));
        assert!(format!("{}", i) == "-11");
        assert!(format!("{:?}", i) == "-11");
        assert!(format!("{:b}", i) == "-1011");
        assert!(format!("{:#b}", i) == "-0b1011");
        assert!(format!("{:o}", i) == "-13");
        assert!(format!("{:#o}", i) == "-0o13");
        assert!(format!("{:x}", i) == "-b");
        assert!(format!("{:X}", i) == "-B");
        assert!(format!("{:8x}", i) == "      -b");
        assert!(format!("{:08X}", i) == "-000000B");
        assert!(format!("{:#08x}", i) == "-0x0000b");
        assert!(format!("{:#8X}", i) == "    -0xB");
    }

    #[test]
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert!(gmp::NAIL_BITS == 0);
        assert!(gmp::NUMB_BITS == gmp::LIMB_BITS);
        assert!(gmp::NUMB_BITS as usize == 8 * mem::size_of::<gmp::limb_t>());
        // we assume that a limb has 32 or 64 bits.
        assert!(gmp::NUMB_BITS == 32 || gmp::NUMB_BITS == 64);
    }
}
