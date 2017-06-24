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

use {Assign, Integer};
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp::{self, mpq_t};
use inner::{Inner, InnerMut};
use ops::{AddFromAssign, DivFromAssign, MulFromAssign, NegAssign, Pow,
          PowAssign, SubFromAssign};
use rational::SmallRational;
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_char, c_int};
use std::str::FromStr;

/// An arbitrary-precision rational number.
///
/// A rational number is made up of a numerator
/// [`Integer`](struct.Integer.html) and denominator
/// [`Integer`](struct.Integer.html). After rational number functions,
/// the number is always in canonical form, that is, the denominator
/// is always greater than zero, and there are no common factors. Zero
/// is stored as 0/1.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
/// let r = Rational::from((-12, 15));
/// let recip = Rational::from(r.recip_ref());
/// assert_eq!(recip, (-5, 4));
/// assert_eq!(recip.to_f32(), -1.25);
/// // The numerator and denominator are stored in canonical form.
/// let (num, den) = r.into_numer_denom();
/// assert_eq!(num, -4);
/// assert_eq!(den, 5);
/// ```
pub struct Rational {
    inner: mpq_t,
}

impl Default for Rational {
    #[inline]
    fn default() -> Rational {
        Rational::new()
    }
}

impl Clone for Rational {
    #[inline]
    fn clone(&self) -> Rational {
        let mut ret = Rational::new();
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Rational) {
        self.assign(source);
    }
}

impl Drop for Rational {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(self.inner_mut());
        }
    }
}

impl Rational {
    /// Constructs a new arbitrary-precision rational number with
    /// value 0.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::new();
    /// assert_eq!(r, 0);
    /// ```
    #[inline]
    pub fn new() -> Rational {
        unsafe {
            let mut ret: Rational = mem::uninitialized();
            gmp::mpq_init(ret.inner_mut());
            ret
        }
    }

    /// Creates a `Rational` from an `f32` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f32;
    /// let r = Rational::from_f32(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f32(f32::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    #[inline]
    pub fn from_f32(val: f32) -> Option<Rational> {
        Rational::from_f64(val as f64)
    }

    /// Creates a `Rational` from an `f64` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f64;
    /// let r = Rational::from_f64(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    #[inline]
    pub fn from_f64(val: f64) -> Option<Rational> {
        if val.is_finite() {
            let mut r = Rational::new();
            r.assign_f64(val).unwrap();
            Some(r)
        } else {
            None
        }
    }

    /// Parses a `Rational` number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r1 = Rational::from_str_radix("ff/a", 16).unwrap();
    /// assert_eq!(r1, (255, 10));
    /// let r2 = Rational::from_str_radix("+ff0/a0", 16).unwrap();
    /// assert_eq!(r2, (0xff0, 0xa0));
    /// assert_eq!(*r2.numer(), 51);
    /// assert_eq!(*r2.denom(), 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str_radix(src, radix)?;
        Ok(r)
    }

    /// Checks if a `Rational` number can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Rational` number. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// The string must contain a numerator, and may contain a
    /// denominator; the numberator and denominator are separated with
    /// a `'/'`. The numerator can start with an optional minus or
    /// plus sign.
    ///
    /// Whitespace is not allowed anywhere in the string, including in
    /// the beginning and end and around the `'/'`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let valid1 = Rational::valid_str_radix("12/23", 4);
    /// let r1 = Rational::from(valid1.unwrap());
    /// assert_eq!(r1, (2 + 4 * 1, 3 + 4 * 2));
    /// let valid2 = Rational::valid_str_radix("12/yz", 36);
    /// let r2 = Rational::from(valid2.unwrap());
    /// assert_eq!(r2, (2 + 36 * 1, 35 + 36 * 34));
    ///
    /// let invalid = Rational::valid_str_radix("12 / 23", 4);
    /// let invalid_f = Rational::from_str_radix("12 / 23", 4);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidRational, ParseRationalError> {
        use self::ParseRationalError as Error;
        use self::ParseErrorKind as Kind;

        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let bytes = src.as_bytes();
        let (skip_plus, iter) = match bytes.get(0) {
            Some(&b'+') => (&bytes[1..], bytes[1..].iter()),
            Some(&b'-') => (bytes, bytes[1..].iter()),
            _ => (bytes, bytes.iter()),
        };
        let mut got_digit = false;
        let mut denom = false;
        let mut denom_non_zero = false;
        for b in iter {
            if *b == b'/' {
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
            let digit_value = match *b {
                b'0'...b'9' => *b - b'0',
                b'a'...b'z' => *b - b'a' + 10,
                b'A'...b'Z' => *b - b'A' + 10,
                _ => Err(Error { kind: Kind::InvalidDigit })?,
            };
            if digit_value >= radix as u8 {
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
        let v = ValidRational {
            bytes: skip_plus,
            radix: radix,
        };
        Ok(v)
    }

    /// Converts to an [`Integer`](struct.Integer.html), rounding
    /// towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let pos = Rational::from((139, 10));
    /// let posi = pos.to_integer();
    /// assert_eq!(posi, 13);
    /// let neg = Rational::from((-139, 10));
    /// let negi = neg.to_integer();
    /// assert_eq!(negi, -13);
    /// ```
    #[inline]
    pub fn to_integer(&self) -> Integer {
        let mut i = Integer::new();
        self.copy_to_integer(&mut i);
        i
    }

    /// Converts to an [`Integer`](struct.Integer.html) inside `i`,
    /// rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Integer, Rational};
    /// let mut i = Integer::new();
    /// assert_eq!(i, 0);
    /// let pos = Rational::from((139, 10));
    /// pos.copy_to_integer(&mut i);
    /// assert_eq!(i, 13);
    /// let neg = Rational::from((-139, 10));
    /// neg.copy_to_integer(&mut i);
    /// assert_eq!(i, -13);
    /// ```
    #[inline]
    pub fn copy_to_integer(&self, i: &mut Integer) {
        unsafe {
            gmp::mpz_set_q(i.inner_mut(), self.inner());
        }
    }

    /// Converts to an `f32`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use rug::rational::SmallRational;
    /// use std::f32;
    /// let min = Rational::from_f32(f32::MIN).unwrap();
    /// let minus_small = min - &*SmallRational::from((7, 2));
    /// // minus_small is truncated to f32::MIN
    /// assert_eq!(minus_small.to_f32(), f32::MIN);
    /// let times_three_two = minus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too small
    /// assert_eq!(times_three_two.to_f32(), f32::NEG_INFINITY);
    /// ```
    #[inline]
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

    /// Converts to an `f64`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use rug::rational::SmallRational;
    /// use std::f64;
    ///
    /// // An `f64` has 53 bits of precision.
    /// let exact = 0x1f_1234_5678_9aff_u64;
    /// let den = 0x1000_u64;
    /// let r = Rational::from((exact, den));
    /// assert_eq!(r.to_f64(), exact as f64 / den as f64);
    ///
    /// // large has 56 ones
    /// let large = 0xff_1234_5678_9aff_u64;
    /// // trunc has 53 ones followed by 3 zeros
    /// let trunc = 0xff_1234_5678_9af8_u64;
    /// let j = Rational::from((large, den));
    /// assert_eq!(j.to_f64(), trunc as f64 / den as f64);
    ///
    /// let max = Rational::from_f64(f64::MAX).unwrap();
    /// let plus_small = max + &*SmallRational::from((7, 2));
    /// // plus_small is truncated to f64::MAX
    /// assert_eq!(plus_small.to_f64(), f64::MAX);
    /// let times_three_two = plus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too large
    /// assert_eq!(times_three_two.to_f64(), f64::INFINITY);
    /// ```
    #[inline]
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(self.inner()) }
    }

    /// Returns a string representation for the specified `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r1 = Rational::from(0);
    /// assert_eq!(r1.to_string_radix(10), "0");
    /// let r2 = Rational::from((15, 5));
    /// assert_eq!(r2.to_string_radix(10), "3");
    /// let r3 = Rational::from((10, -6));
    /// assert_eq!(r3.to_string_radix(10), "-5/3");
    /// assert_eq!(r3.to_string_radix(5), "-10/3");
    /// ```
    ///
    /// #Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix(&self, radix: i32) -> String {
        make_string(self, radix, false)
    }

    /// Assigns from an `f32` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f32;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f32(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f32(f32::NAN);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
    #[inline]
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val as f64)
    }

    /// Assigns from an `f64` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f64(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f64(1.0 / 0.0);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
    #[inline]
    pub fn assign_f64(&mut self, val: f64) -> Result<(), ()> {
        if val.is_finite() {
            unsafe {
                gmp::mpq_set_d(self.inner_mut(), val);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    /// Parses a `Rational` number from a string.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_str("1/0");
    /// assert!(ret.is_err());
    /// r.assign_str("-24/2").unwrap();
    /// assert_eq!(*r.numer(), -12);
    /// assert_eq!(*r.denom(), 1);
    /// ```
    #[inline]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseRationalError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Rational` number from a string with the specified
    /// radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// r.assign_str_radix("ff/a", 16).unwrap();
    /// assert_eq!(r, (255, 10));
    /// r.assign_str_radix("+ff0/a0", 16).unwrap();
    /// assert_eq!(r, (255, 10));
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
    ) -> Result<(), ParseRationalError> {
        self.assign(Rational::valid_str_radix(src, radix)?);
        Ok(())
    }

    /// Borrows the numerator as an `Integer`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.numer(), -3)
    /// ```
    #[inline]
    pub fn numer(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_numref_const(self.inner());
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the denominator as an
    /// [`Integer`](struct.Integer.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.denom(), 5);
    /// ```
    #[inline]
    pub fn denom(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_denref_const(self.inner());
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the numerator and denominator as
    /// [`Integer`](struct.Integer.html) values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.as_numer_denom();
    /// assert_eq!(*num, -3);
    /// assert_eq!(*den, 5);
    /// ```
    #[inline]
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
    /// use rug::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // change r from 3/5 to 4/8, which is equal to 1/2
    ///     *num_den.num() += 1;
    ///     *num_den.den() += 3;
    ///     // borrow ends here
    /// }
    /// let num_den = r.as_numer_denom();
    /// assert_eq!(*num_den.0, 1);
    /// assert_eq!(*num_den.1, 2);
    /// ```
    ///
    /// If the mutable value is leaked, the denominator is lost when
    /// the borrow ends.
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::mem;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // try change r from 3/5 to 4/8
    ///     *num_den.num() += 1;
    ///     *num_den.den() += 3;
    ///     // forget num_den, so no canonicalization takes place
    ///     mem::forget(num_den)
    ///     // borrow ends here, but nothing happens
    /// }
    /// // because of the leak, 4/8 has become 4/1
    /// let num_den = r.as_numer_denom();
    /// assert_eq!(*num_den.0, 4);
    /// assert_eq!(*num_den.1, 1);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the borrow ends.
    pub fn as_mut_numer_denom(&mut self) -> MutNumerDenom {
        // We swap in a denominator of 1 so that if the
        // `MutNumerDenom` is leaked, we don't end up with an
        // uncanonicalized rational number.
        unsafe {
            let numer_ptr = gmp::mpq_numref(self.inner_mut());
            let denom_ptr = gmp::mpq_denref(self.inner_mut());
            let mut acting_denom = Integer::from(1);
            mem::swap(acting_denom.inner_mut(), &mut *denom_ptr);
            MutNumerDenom {
                num: &mut *(numer_ptr as *mut Integer),
                den_place: &mut *(denom_ptr as *mut Integer),
                den_actual: acting_denom,
            }
        }
    }

    /// Borrows the numerator and denominator mutably without
    /// canonicalizing aftwerwards.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not canonicalize the
    /// rational number when the borrow ends. The rest of the library
    /// assumes that `Rational` structures keep their numerators and
    /// denominators canonicalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let (num, den) = unsafe {
    ///         r.as_mut_numer_denom_no_canonicalization()
    ///     };
    ///     // Add one to r by adding den to num. Since num and den
    ///     // are relatively prime, r remains canonicalized.
    ///     *num += &*den;
    /// }
    /// assert_eq!(r, (8, 5));
    /// ```
    #[inline]
    pub unsafe fn as_mut_numer_denom_no_canonicalization(
        &mut self,
    ) -> (&mut Integer, &mut Integer) {

        (
            &mut *(gmp::mpq_numref(self.inner_mut()) as *mut _),
            &mut *(gmp::mpq_denref(self.inner_mut()) as *mut _),
        )
    }

    /// Converts into numerator and denominator integers.
    ///
    /// This function reuses the allocated memory and does not
    /// allocate any new memory.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.into_numer_denom();
    /// assert_eq!(num, -3);
    /// assert_eq!(den, 5);
    /// ```
    #[inline]
    pub fn into_numer_denom(mut self) -> (Integer, Integer) {
        let (mut numer, mut denom) = unsafe { mem::uninitialized() };
        {
            let mut self_numer_denom = self.as_mut_numer_denom();
            mem::swap(&mut numer, self_numer_denom.num());
            mem::swap(&mut denom, self_numer_denom.den());
            // do not canonicalize uninitialized values
            mem::forget(self_numer_denom);
        }
        mem::forget(self);
        (numer, denom)
    }

    /// Returns `Ordering::Less` if the number is less than zero,
    /// `Ordering::Greater` if it is greater than zero, or
    /// `Ordering::Equal` if it is equal to zero.
    #[inline]
    pub fn sign(&self) -> Ordering {
        self.numer().sign()
    }

    math_op1! {
        Rational;
        gmp::mpq_abs;
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// assert_eq!(*r.abs(), (100, 17));
        /// assert_eq!(r, (100, 17));
        /// ```
        fn abs();
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let rr = r.abs_ref();
        /// let abs = Rational::from(rr);
        /// assert_eq!(abs, (100, 17));
        /// ```
        fn abs_ref -> AbsRef;
    }
    math_op1! {
        Rational;
        xgmp::mpq_inv_check_0;
        /// Computes the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// assert_eq!(*r.recip(), (-17, 100));
        /// assert_eq!(r, (-17, 100));
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        fn recip();
        /// Computes the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let rr = r.recip_ref();
        /// let recip = Rational::from(rr);
        /// assert_eq!(recip, (-17, 100));
        /// ```
        fn recip_ref -> RecipRef;
    }

    /// Rounds the number upwards (towards plus infinity).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rational::SmallRational;
    /// let mut ceil = Integer::new();
    /// ceil.assign(SmallRational::from(-1).ceil_ref());
    /// assert_eq!(ceil, -1);
    /// ceil.assign(SmallRational::from((-1, 2)).ceil_ref());
    /// assert_eq!(ceil, 0);
    /// ceil.assign(SmallRational::from(0).ceil_ref());
    /// assert_eq!(ceil, 0);
    /// ceil.assign(SmallRational::from((1, 2)).ceil_ref());
    /// assert_eq!(ceil, 1);
    /// ceil.assign(SmallRational::from(1).ceil_ref());
    /// assert_eq!(ceil, 1);
    /// ```
    #[inline]
    pub fn ceil_ref(&self) -> CeilRef {
        CeilRef { ref_self: self }
    }

    /// Rounds the number downwards (towards minus infinity).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rational::SmallRational;
    /// let mut floor = Integer::new();
    /// floor.assign(SmallRational::from(-1).floor_ref());
    /// assert_eq!(floor, -1);
    /// floor.assign(SmallRational::from((-1, 2)).floor_ref());
    /// assert_eq!(floor, -1);
    /// floor.assign(SmallRational::from(0).floor_ref());
    /// assert_eq!(floor, 0);
    /// floor.assign(SmallRational::from((1, 2)).floor_ref());
    /// assert_eq!(floor, 0);
    /// floor.assign(SmallRational::from(1).floor_ref());
    /// assert_eq!(floor, 1);
    /// ```
    #[inline]
    pub fn floor_ref(&self) -> FloorRef {
        FloorRef { ref_self: self }
    }

    /// Rounds the number to the nearest integer. When the number lies
    /// exactly between two integers, it is rounded away from zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rational::SmallRational;
    /// let mut round = Integer::new();
    /// round.assign(SmallRational::from((-17, 10)).round_ref());
    /// assert_eq!(round, -2);
    /// round.assign(SmallRational::from((-15, 10)).round_ref());
    /// assert_eq!(round, -2);
    /// round.assign(SmallRational::from((-13, 10)).round_ref());
    /// assert_eq!(round, -1);
    /// round.assign(SmallRational::from((13, 10)).round_ref());
    /// assert_eq!(round, 1);
    /// round.assign(SmallRational::from((15, 10)).round_ref());
    /// assert_eq!(round, 2);
    /// round.assign(SmallRational::from((17, 10)).round_ref());
    /// assert_eq!(round, 2);
    /// ```
    #[inline]
    pub fn round_ref(&self) -> RoundRef {
        RoundRef { ref_self: self }
    }

    /// Rounds the number towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rational::SmallRational;
    /// let mut trunc = Integer::new();
    /// trunc.assign(SmallRational::from((-21, 10)).trunc_ref());
    /// assert_eq!(trunc, -2);
    /// trunc.assign(SmallRational::from((-17, 10)).trunc_ref());
    /// assert_eq!(trunc, -1);
    /// trunc.assign(SmallRational::from((13, 10)).trunc_ref());
    /// assert_eq!(trunc, 1);
    /// trunc.assign(SmallRational::from((19, 10)).trunc_ref());
    /// assert_eq!(trunc, 1);
    /// ```
    #[inline]
    pub fn trunc_ref(&self) -> TruncRef {
        TruncRef { ref_self: self }
    }

    math_op1! {
        Rational;
        xgmp::mpq_fract;
        /// Computes the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -5 15/17
        /// let mut r = Rational::from((-100, 17));
        /// assert_eq!(*r.fract(), (-15, 17));
        /// ```
        fn fract();
        /// Computes the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let rr = r.fract_ref();
        /// let fract = Rational::from(rr);
        /// assert_eq!(fract, (-15, 17));
        /// ```
        fn fract_ref -> FractRef;
    }

    /// Computes the fractional and truncated parts of the number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Integer, Rational};
    /// // -100/17 = -5 15/17
    /// let mut r = Rational::from((-100, 17));
    /// let mut whole = Integer::new();
    /// r.fract_trunc(&mut whole);
    /// assert_eq!(whole, -5);
    /// assert_eq!(r, (-15, 17));
    /// ```
    #[inline]
    pub fn fract_trunc(&mut self, trunc: &mut Integer) {
        unsafe {
            xgmp::mpq_fract_trunc(
                self.inner_mut(),
                trunc.inner_mut(),
                self.inner(),
            );
        }
    }

    /// Computes the fractional and truncated parts of the number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer, Rational};
    /// // -100/17 = -5 15/17
    /// let r = Rational::from((-100, 17));
    /// let rr = r.fract_trunc_ref();
    /// let (mut proper, mut whole) = (Rational::new(), Integer::new());
    /// (&mut proper, &mut whole).assign(rr);
    /// assert_eq!(whole, -5);
    /// assert_eq!(proper, (-15, 17));
    /// ```
    #[inline]
    pub fn fract_trunc_ref(&self) -> FractTruncRef {
        FractTruncRef { ref_self: self }
    }
}

from_borrow! { &'a Rational => Rational }

impl From<Integer> for Rational {
    /// Constructs a `Rational` number from an
    /// [`Integer`](struct.Integer.html).
    ///
    /// This constructor allocates one new
    /// [`Integer`](struct.Integer.html) and reuses the allocation for
    /// `val`.
    #[inline]
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_borrow! { &'a Integer => Rational }

impl From<(Integer, Integer)> for Rational {
    /// Constructs a `Rational` number from a numerator
    /// [`Integer`](struct.Integer.html) and denominator
    /// [`Integer`](struct.Integer.html).
    ///
    /// This constructor does not allocate, as it reuses the
    /// [`Integer`](struct.Integer.html) components.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    #[inline]
    fn from((mut num, mut den): (Integer, Integer)) -> Rational {
        assert_ne!(den.sign(), Ordering::Equal, "division by zero");
        let mut dst: Rational = unsafe { mem::uninitialized() };
        {
            let mut num_den = dst.as_mut_numer_denom();
            mem::swap(&mut num, num_den.num());
            mem::swap(&mut den, num_den.den());
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

from_borrow! { (&'a Integer, &'a Integer) => Rational }

macro_rules! from {
    { $Src:ty => $Dst:ty } => {
        impl From<$Src> for $Dst {
            #[inline]
            fn from(t: $Src) -> $Dst {
                let mut ret = <$Dst>::new();
                ret.assign(t);
                ret
            }
        }
    }
}

from! { i32 => Rational }
from! { i64 => Rational }
from! { u32 => Rational }
from! { u64 => Rational }
from! { (i32, i32) => Rational }
from! { (i64, i64) => Rational }
from! { (i32, u32) => Rational }
from! { (i64, u64) => Rational }
from! { (u32, i32) => Rational }
from! { (u64, i64) => Rational }
from! { (u32, u32) => Rational }
from! { (u64, u64) => Rational }

impl FromStr for Rational {
    type Err = ParseRationalError;
    #[inline]
    fn from_str(src: &str) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str(src)?;
        Ok(r)
    }
}

impl Display for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl Assign for Rational {
    #[inline]
    fn assign(&mut self, mut other: Rational) {
        self.assign(&other);
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Rational> for Rational {
    #[inline]
    fn assign(&mut self, other: &'a Rational) {
        unsafe {
            gmp::mpq_set(self.inner_mut(), other.inner());
        }
    }
}

impl<'a> Assign<&'a Integer> for Rational {
    #[inline]
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(self.inner_mut(), val.inner());
        }
    }
}

macro_rules! assign {
    { $T:ty } => {
        impl Assign<$T> for Rational {
            #[inline]
            fn assign(&mut self, t: $T) {
                // no need to canonicalize, as denominator will be 1.
                let num_den =
                    unsafe { self.as_mut_numer_denom_no_canonicalization() };
                num_den.0.assign(t);
                num_den.1.assign(1);
            }
        }
    };
}

assign!{ Integer }
assign!{ i32 }
assign!{ i64 }
assign!{ u32 }
assign!{ u64 }

impl<T, U> Assign<(T, U)> for Rational
where
    Integer: Assign<T>,
    Integer: Assign<U>,
{
    #[inline]
    fn assign(&mut self, (num, den): (T, U)) {
        let mut num_den = self.as_mut_numer_denom();
        num_den.num().assign(num);
        num_den.den().assign(den);
    }
}

ref_math_op1! { Rational; gmp::mpq_abs; struct AbsRef {} }
ref_math_op1! { Rational; xgmp::mpq_inv_check_0; struct RecipRef {} }

pub struct CeilRef<'a> {
    ref_self: &'a Rational,
}

impl<'a> Assign<CeilRef<'a>> for Integer {
    #[inline]
    fn assign(&mut self, src: CeilRef<'a>) {
        unsafe {
            xgmp::mpq_ceil(self.inner_mut(), src.ref_self.inner());
        }
    }
}

pub struct FloorRef<'a> {
    ref_self: &'a Rational,
}

impl<'a> Assign<FloorRef<'a>> for Integer {
    #[inline]
    fn assign(&mut self, src: FloorRef<'a>) {
        unsafe {
            xgmp::mpq_floor(self.inner_mut(), src.ref_self.inner());
        }
    }
}

pub struct RoundRef<'a> {
    ref_self: &'a Rational,
}

impl<'a> Assign<RoundRef<'a>> for Integer {
    #[inline]
    fn assign(&mut self, src: RoundRef<'a>) {
        unsafe {
            xgmp::mpq_round(self.inner_mut(), src.ref_self.inner());
        }
    }
}

pub struct TruncRef<'a> {
    ref_self: &'a Rational,
}

impl<'a> Assign<TruncRef<'a>> for Integer {
    #[inline]
    fn assign(&mut self, src: TruncRef<'a>) {
        unsafe {
            xgmp::mpq_trunc(self.inner_mut(), src.ref_self.inner());
        }
    }
}

ref_math_op1! { Rational; xgmp::mpq_fract; struct FractRef {} }

pub struct FractTruncRef<'a> {
    ref_self: &'a Rational,
}

impl<'a> Assign<FractTruncRef<'a>> for (&'a mut Rational, &'a mut Integer) {
    #[inline]
    fn assign(&mut self, src: FractTruncRef<'a>) {
        unsafe {
            xgmp::mpq_fract_trunc(
                self.0.inner_mut(),
                self.1.inner_mut(),
                src.ref_self.inner(),
            );
        }
    }
}

arith_unary! { Rational; gmp::mpq_neg; Neg neg; NegAssign neg_assign; NegRef }
arith_binary! {
    Rational;
    gmp::mpq_add;
    Add add;
    AddAssign add_assign;
    AddFromAssign add_from_assign;
    AddRef
}
arith_binary! {
    Rational;
    gmp::mpq_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFromAssign sub_from_assign;
    SubRef
}
arith_binary! {
    Rational;
    gmp::mpq_mul;
    Mul mul;
    MulAssign mul_assign;
    MulFromAssign mul_from_assign;
    MulRef
}
arith_binary! {
    Rational;
    gmp::mpq_div;
    Div div;
    DivAssign div_assign;
    DivFromAssign div_from_assign;
    DivRef
}

arith_prim! {
    Rational;
    xgmp::mpq_mul_2exp_si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlRefI32
}
arith_prim! {
    Rational;
    xgmp::mpq_div_2exp_si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrRefI32
}
arith_prim! {
    Rational; xgmp::mpq_pow_si; Pow pow; PowAssign pow_assign; i32; PowRefI32
}

arith_prim! {
    Rational; gmp::mpq_mul_2exp; Shl shl; ShlAssign shl_assign; u32; ShlRefU32
}
arith_prim! {
    Rational; gmp::mpq_div_2exp; Shr shr; ShrAssign shr_assign; u32; ShrRefU32
}
arith_prim! {
    Rational; xgmp::mpq_pow_ui; Pow pow; PowAssign pow_assign; u32; PowRefU32
}

impl Eq for Rational {}

impl Ord for Rational {
    #[inline]
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    #[inline]
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $T:ty, $eq:expr, $cmp:expr } => {
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                $eq(self.inner(), other)
            }
        }

        impl PartialEq<Rational> for $T {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<$T> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                Some($cmp(self.inner(), other))
            }
        }

        impl PartialOrd<Rational> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    }
}

cmp! {
    Integer,
    |r, t: &Integer| unsafe { gmp::mpq_cmp_z(r, t.inner()) } == 0,
    |r, t: &Integer| unsafe { gmp::mpq_cmp_z(r, t.inner()) }.cmp(&0)
}
cmp! {
    i32,
    |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1) } == 0,
    |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1) }.cmp(&0)
}
cmp! {
    u32,
    |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1) } == 0,
    |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1) }.cmp(&0)
}

macro_rules! cmp_small_rat {
    { $T:ty } => {
        cmp! {
            $T,
            |r, t: &$T| unsafe {
                gmp::mpq_equal(r, SmallRational::from(*t).inner())
            } != 0,
            |r, t: &$T| unsafe {
                gmp::mpq_cmp(r, SmallRational::from(*t).inner())
            }.cmp(&0)
        }
    };
}

cmp_small_rat! { i64 }
cmp_small_rat! { u64 }
cmp_small_rat! { (i32, i32) }
cmp_small_rat! { (i64, i64) }
cmp_small_rat! { (i32, u32) }
cmp_small_rat! { (i64, u64) }
cmp_small_rat! { (u32, i32) }
cmp_small_rat! { (u64, i64) }
cmp_small_rat! { (u32, u32) }
cmp_small_rat! { (u64, u64) }

fn make_string(r: &Rational, radix: i32, to_upper: bool) -> String {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let (num, den) = r.as_numer_denom();
    let n_size = unsafe { gmp::mpz_sizeinbase(num.inner(), radix) };
    let d_size = unsafe { gmp::mpz_sizeinbase(den.inner(), radix) };
    // n_size + d_size + 3 for '-', '/' and nul
    let size = n_size.checked_add(d_size).unwrap().checked_add(3).unwrap();
    let mut buf = Vec::<u8>::with_capacity(size);
    let case_radix = if to_upper { -radix } else { radix };
    unsafe {
        buf.set_len(size);
        gmp::mpq_get_str(
            buf.as_mut_ptr() as *mut c_char,
            case_radix as c_int,
            r.inner(),
        );
        let nul_index = buf.iter().position(|&x| x == 0).unwrap();
        buf.set_len(nul_index);
        String::from_utf8_unchecked(buf)
    }
}

fn fmt_radix(
    r: &Rational,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let s = make_string(r, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

/// A validated string that can always be converted to a `Rational`.
///
/// See the [`Rational::valid_str_radix`]
/// (../struct.Rational.html#method.valid_str_radix) method.
#[derive(Clone, Debug)]
pub struct ValidRational<'a> {
    bytes: &'a [u8],
    radix: i32,
}

from_borrow! { ValidRational<'a> => Rational }

impl<'a> Assign<ValidRational<'a>> for Rational {
    #[inline]
    fn assign(&mut self, rhs: ValidRational) {
        let mut v = Vec::<u8>::with_capacity(rhs.bytes.len() + 1);
        v.extend_from_slice(rhs.bytes);
        v.push(0);
        let err = unsafe {
            let c_str = CStr::from_bytes_with_nul_unchecked(&v);
            gmp::mpq_set_str(self.inner_mut(), c_str.as_ptr(), rhs.radix.into())
        };
        assert_eq!(err, 0);
        unsafe {
            gmp::mpq_canonicalize(self.inner_mut());
        }
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
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

/// Used to borrow the numerator and denominator of a
/// [`Rational`](../struct.Rational.html) number mutably.
///
/// The [`Rational`](../struct.Rational.html) number is canonicalized
/// when the borrow ends. See the
/// [`Rational::as_mut_numer_denom`][mutnumden] method.
///
/// [mutnumden]: ../struct.Rational.html#method.as_mut_numer_denom
pub struct MutNumerDenom<'a> {
    num: &'a mut Integer,
    den_place: &'a mut Integer,
    den_actual: Integer,
}

impl<'a> MutNumerDenom<'a> {
    /// Gets the mutable numerator.
    #[inline]
    pub fn num(&mut self) -> &mut Integer {
        self.num
    }
    /// Gets the mutable denominator.
    #[inline]
    pub fn den(&mut self) -> &mut Integer {
        &mut self.den_actual
    }
    /// Gets the mutable numerator and denominator.
    #[inline]
    pub fn num_den(&mut self) -> (&mut Integer, &mut Integer) {
        (self.num, &mut self.den_actual)
    }
}

impl<'a> Drop for MutNumerDenom<'a> {
    #[inline]
    fn drop(&mut self) {
        assert_ne!(self.den_actual.sign(), Ordering::Equal, "division by zero");
        unsafe {
            // We can finally place the actual denominator in its
            // proper place inside the rational number.
            mem::swap(&mut self.den_actual, self.den_place);

            let rat_num = self.num.inner_mut();
            let rat_den = self.den_place.inner_mut();
            let mut canon: mpq_t = mem::uninitialized();
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

unsafe impl Send for Rational {}
unsafe impl Sync for Rational {}

impl Inner for Rational {
    type Output = mpq_t;
    #[inline]
    fn inner(&self) -> &mpq_t {
        &self.inner
    }
}

impl InnerMut for Rational {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut mpq_t {
        &mut self.inner
    }
}
