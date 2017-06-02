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

use SmallRational;
use gmp_mpfr_sys::gmp::{self, mpq_t};
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
use std::os::raw::{c_char, c_int};
use std::str::FromStr;
use xgmp;

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
///     assert_eq!(num, -4);
///     assert_eq!(den, 5);
///     let one = Rational::from((num, Integer::from(-4)));
///     assert_eq!(one, 1);
/// }
/// ```
pub struct Rational {
    inner: mpq_t,
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

impl Drop for Rational {
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(self.inner_mut());
        }
    }
}

macro_rules! math_op1 {
    {
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_hold:meta])*
        fn $method_hold:ident -> $Hold:ident;
        $func:path
    } => {
        $(#[$attr])*
        pub fn $method(
            &mut self,
            $($param: $T,)*
        ) -> &mut Rational {
            unsafe {
                $func(
                    self.inner_mut(),
                    self.inner(),
                    $($param.into(),)*
                );
            }
            self
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

macro_rules! hold_math_op1 {
    {
        $(#[$attr_hold:meta])*
        struct $Hold:ident { $($param:ident: $T:ty),* };
        $func:path
    } => {
        $(#[$attr_hold])*
        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            hold_self: &'a Rational,
            $($param: $T,)*
        }

        from_borrow! { $Hold<'a> }

        impl<'a> Assign<$Hold<'a>> for Rational {
            fn assign(&mut self, src: $Hold<'a>) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        src.hold_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }
    };
}

impl Rational {
    /// Constructs a new arbitrary-precision rational number with
    /// value 0.
    ///
    /// # Examples
    /// ```rust
    /// use rugrat::Rational;
    /// let r = Rational::new();
    /// assert_eq!(r, 0);
    /// ```
    pub fn new() -> Rational {
        let mut inner: mpq_t = unsafe { mem::uninitialized() };
        unsafe {
            gmp::mpq_init(&mut inner);
        }
        Rational { inner: inner }
    }

    /// Creates a `Rational` from an `f32` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// use std::f32;
    /// let r = Rational::from_f32(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f32(f32::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    pub fn from_f32(val: f32) -> Option<Rational> {
        Rational::from_f64(val as f64)
    }

    /// Creates a `Rational` from an `f64` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// use std::f64;
    /// let r = Rational::from_f64(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
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
    /// use rugrat::Rational;
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
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// assert!(Rational::valid_str_radix("123/321", 4).is_ok());
    /// assert!(Rational::valid_str_radix("123/xyz", 36).is_ok());
    ///
    /// let invalid_valid = Rational::valid_str_radix("1/123", 3);
    /// let invalid_from = Rational::from_str_radix("1/123", 3);
    /// assert_eq!(invalid_valid.unwrap_err(), invalid_from.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<(), ParseRationalError> {
        check_str_radix(src, radix).map(|_| ())
    }


    /// Converts `self` to an `Integer`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let pos = Rational::from((139, 10));
    /// let posi = pos.to_integer();
    /// assert_eq!(posi, 13);
    /// let neg = Rational::from((-139, 10));
    /// let negi = neg.to_integer();
    /// assert_eq!(negi, -13);
    /// ```
    pub fn to_integer(&self) -> Integer {
        let mut i = Integer::new();
        self.copy_to_integer(&mut i);
        i
    }

    /// Converts `self` to an `Integer` inside `i`, rounding towards
    /// zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugrat;
    /// use rugint::Integer;
    /// use rugrat::Rational;
    ///
    /// fn main() {
    ///     let mut i = Integer::new();
    ///     assert_eq!(i, 0);
    ///     let pos = Rational::from((139, 10));
    ///     pos.copy_to_integer(&mut i);
    ///     assert_eq!(i, 13);
    ///     let neg = Rational::from((-139, 10));
    ///     neg.copy_to_integer(&mut i);
    ///     assert_eq!(i, -13);
    /// }
    /// ```
    pub fn copy_to_integer(&self, i: &mut Integer) {
        unsafe {
            gmp::mpz_set_q(i.inner_mut(), self.inner());
        }
    }

    /// Converts `self` to an `f32`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::{Rational, SmallRational};
    /// use std::f32;
    /// let min = Rational::from_f32(f32::MIN).unwrap();
    /// let minus_small = min - &*SmallRational::from((7, 2));
    /// // minus_small is truncated to f32::MIN
    /// assert_eq!(minus_small.to_f32(), f32::MIN);
    /// let times_three_two = minus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too small
    /// assert_eq!(times_three_two.to_f32(), f32::NEG_INFINITY);
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

    /// Converts to an `f64`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::{Rational, SmallRational};
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
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(self.inner()) }
    }

    /// Returns a string representation of `self` for the specified
    /// `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
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
    pub fn to_string_radix(&self, radix: i32) -> String {
        make_string(self, radix, false)
    }

    /// Assigns from an `f32` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// use std::f32;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f32(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f32(f32::NAN);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val as f64)
    }

    /// Assigns from an `f64` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f64(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f64(1.0 / 0.0);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
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
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_str("1/0");
    /// assert!(ret.is_err());
    /// r.assign_str("-24/2").unwrap();
    /// assert_eq!(*r.numer(), -12);
    /// assert_eq!(*r.denom(), 1);
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
    /// assert_eq!(r, (255, 10));
    /// r.assign_str_radix("+ff0/a0", 16).unwrap();
    /// assert_eq!(r, (255, 10));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseRationalError> {
        let s = check_str_radix(src, radix)?;
        let c_str = CString::new(s).unwrap();
        let err = unsafe {
            gmp::mpq_set_str(self.inner_mut(), c_str.as_ptr(), radix.into())
        };
        assert_eq!(err, 0);
        unsafe {
            gmp::mpq_canonicalize(self.inner_mut());
        }
        Ok(())
    }

    /// Borrows the numerator as an `Integer`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.numer(), -3)
    /// ```
    pub fn numer(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_numref(self.inner() as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the denominator as an `Integer`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.denom(), 5);
    /// ```
    pub fn denom(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_denref(self.inner() as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the numerator and denominator as `Integer`s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.as_numer_denom();
    /// assert_eq!(*num, -3);
    /// assert_eq!(*den, 5);
    /// ```
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
    /// assert_eq!(*num_den.0, 1);
    /// assert_eq!(*num_den.1, 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the borrow ends.
    pub fn as_mut_numer_denom(&mut self) -> MutNumerDenom {
        unsafe {
            let numer_ptr = gmp::mpq_numref(self.inner_mut());
            let denom_ptr = gmp::mpq_denref(self.inner_mut());
            MutNumerDenom(
                &mut *(numer_ptr as *mut Integer),
                &mut *(denom_ptr as *mut Integer),
            )
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
    /// use rugrat::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let (num, den) = unsafe {
    ///         r.as_mut_numer_denom_no_canonicalization()
    ///     };
    ///     *num -= 7;
    ///     *den += 2;
    /// }
    /// let num_den = r.as_numer_denom();
    /// assert_eq!(*num_den.0, -4);
    /// assert_eq!(*num_den.1, 7);
    /// ```
    pub unsafe fn as_mut_numer_denom_no_canonicalization
        (&mut self)
         -> (&mut Integer, &mut Integer) {

        (&mut *(gmp::mpq_numref(self.inner_mut()) as *mut _),
         &mut *(gmp::mpq_denref(self.inner_mut()) as *mut _))
    }

    /// Converts `self` into numerator and denominator integers,
    /// consuming `self`.
    ///
    /// This function reuses the allocated memory and does not
    /// allocate any new memory.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.into_numer_denom();
    /// assert_eq!(num, -3);
    /// assert_eq!(den, 5);
    /// ```
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

    /// Returns `Less` if `self` is less than zero,
    /// `Greater` if `self` is greater than zero,
    /// or `Equal` if `self` is equal to zero.
    pub fn sign(&self) -> Ordering {
        self.numer().sign()
    }

    math_op1! {
        /// Computes the absolute value of `self`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugrat::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// assert_eq!(*r.abs(), (100, 17));
        /// assert_eq!(r, (100, 17));
        /// ```
        fn abs();
        /// Holds a computation of the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugrat::Rational;
        /// let r = Rational::from((-100, 17));
        /// let hold = r.abs_hold();
        /// let abs = Rational::from(hold);
        /// assert_eq!(abs, (100, 17));
        /// ```
        fn abs_hold -> AbsHold;
        gmp::mpq_abs
    }
    math_op1! {
        /// Computes the reciprocal of `self`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugrat::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// assert_eq!(*r.recip(), (-17, 100));
        /// assert_eq!(r, (-17, 100));
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        fn recip();
        /// Holds a computation of the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rugrat::Rational;
        /// let r = Rational::from((-100, 17));
        /// let hold = r.recip_hold();
        /// let recip = Rational::from(hold);
        /// assert_eq!(recip, (-17, 100));
        /// ```
        fn recip_hold -> RecipHold;
        xgmp::mpq_inv_check_0
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

macro_rules! from_borrow {
    { $T:ty } => {
        impl<'a> From<$T> for Rational {
            fn from(t: $T) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

macro_rules! from {
    { $T:ty } => {
        impl From<$T> for Rational {
            fn from(t: $T) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

from_borrow! { &'a Rational }

impl From<Integer> for Rational {
    /// Constructs a `Rational` number from an `Integer`.
    ///
    /// This constructor allocates one new `Integer` and reuses the
    /// allocation for `val`.
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_borrow! { &'a Integer }

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

from_borrow! { (&'a Integer, &'a Integer) }

from! { i32 }
from! { i64 }
from! { u32 }
from! { u64 }
from! { (i32, i32) }
from! { (i64, i64) }
from! { (i32, u32) }
from! { (i64, u64) }
from! { (u32, i32) }
from! { (u64, i64) }
from! { (u32, u32) }
from! { (u64, u64) }

impl FromStr for Rational {
    type Err = ParseRationalError;
    fn from_str(src: &str) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str(src)?;
        Ok(r)
    }
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

impl Assign for Rational {
    fn assign(&mut self, mut other: Rational) {
        self.assign(&other);
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Rational> for Rational {
    fn assign(&mut self, other: &'a Rational) {
        unsafe {
            gmp::mpq_set(self.inner_mut(), other.inner());
        }
    }
}

impl<'a> Assign<&'a Integer> for Rational {
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(self.inner_mut(), val.inner());
        }
    }
}

macro_rules! assign {
    { $T:ty } => {
        impl Assign<$T> for Rational {
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
    fn assign(&mut self, (num, den): (T, U)) {
        let num_den = self.as_mut_numer_denom();
        num_den.0.assign(num);
        num_den.1.assign(den);
    }
}

hold_math_op1! { struct AbsHold {}; gmp::mpq_abs }
hold_math_op1! { struct RecipHold {}; xgmp::mpq_inv_check_0 }

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Hold: ident
    } => {
        impl $Imp<Rational> for Rational {
            type Output = Rational;
            fn $method(self, op: Rational) -> Rational {
                self.$method(&op)
            }
        }

        impl<'a> $Imp<&'a Rational> for Rational {
            type Output = Rational;
            fn $method(mut self, op: &'a Rational) -> Rational {
                self.$method_assign(op);
                self
            }
        }

        impl $ImpAssign<Rational> for Rational {
            fn $method_assign(&mut self, op: Rational) {
                self.add_assign(&op);
            }
        }

        impl<'a> $ImpAssign<&'a Rational> for Rational {
            fn $method_assign(&mut self, op: &'a Rational) {
                unsafe {
                    $func(self.inner_mut(), self.inner(), op.inner());
                }
            }
        }

        impl<'a> $Imp<&'a Rational> for &'a Rational {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Rational) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        #[derive(Clone, Copy)]
        pub struct $Hold<'a> {
            lhs: &'a Rational,
            rhs: &'a Rational,
        }

        from_borrow! { $Hold<'a> }

        impl<'a> Assign<$Hold<'a>> for Rational {
            fn assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.inner());
                }
            }
        }
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
        arith_binary! {
            $Imp $method, $ImpAssign $method_assign, $func, $Hold
        }

        impl $ImpFromAssign<Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: Rational) {
                self.$method_from_assign(&lhs);
            }
        }

        impl<'a> $ImpFromAssign<&'a Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: &'a Rational) {
                unsafe {
                    $func(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }
    };
}


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
            gmp::mpq_neg(self.inner_mut(), self.inner());
        }
    }
}

impl<'a> Neg for &'a Rational {
    type Output = NegHold<'a>;
    fn neg(self) -> NegHold<'a> {
        NegHold { op: self }
    }
}

#[derive(Clone, Copy)]
pub struct NegHold<'a> {
    op: &'a Rational,
}

from_borrow! { NegHold<'a> }

impl<'a> Assign<NegHold<'a>> for Rational {
    fn assign(&mut self, rhs: NegHold) {
        unsafe {
            gmp::mpq_neg(self.inner_mut(), rhs.op.inner());
        }
    }
}

arith_binary! { Add add, AddAssign add_assign, gmp::mpq_add, AddHold }
arith_noncommut! {
    Sub sub,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    gmp::mpq_sub,
    SubHold
}
arith_binary! { Mul mul, MulAssign mul_assign, gmp::mpq_mul, MulHold }
arith_noncommut! {
    Div div,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    gmp::mpq_div,
    DivHold
}

macro_rules! arith_prim {
    {
        $Imp:ident $method:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
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
                    $func(self.inner_mut(), self.inner(), op.into());
                }
            }
        }

        impl<'a> $Imp<$T> for &'a Rational {
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
            lhs: &'a Rational,
            rhs: $T,
        }

        from_borrow! { $Hold<'a> }

        impl<'a> Assign<$Hold<'a>> for Rational {
            fn assign(&mut self, rhs: $Hold) {
                unsafe {
                    $func(self.inner_mut(), rhs.lhs.inner(), rhs.rhs.into());
                }
            }
        }
    };
}

arith_prim! {
    Shl shl, ShlAssign shl_assign, i32, xgmp::mpq_mul_2exp_si, ShlHoldI32
}
arith_prim! {
    Shr shr, ShrAssign shr_assign, i32, xgmp::mpq_div_2exp_si, ShrHoldI32
}
arith_prim! { Pow pow, PowAssign pow_assign, i32, xgmp::mpq_pow_si, PowHoldI32 }

arith_prim! {
    Shl shl, ShlAssign shl_assign, u32, gmp::mpq_mul_2exp, ShlHoldU32
}
arith_prim! {
    Shr shr, ShrAssign shr_assign, u32, gmp::mpq_div_2exp, ShrHoldU32
}
arith_prim! { Pow pow, PowAssign pow_assign, u32, xgmp::mpq_pow_ui, PowHoldU32 }

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $T:ty, $eq:expr, $cmp:expr } => {
        impl PartialEq<$T> for Rational {
            fn eq(&self, other: &$T) -> bool {
                $eq(self.inner(), other)
            }
        }

        impl PartialEq<Rational> for $T {
            fn eq(&self, other: &Rational) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<$T> for Rational {
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                Some($cmp(self.inner(), other))
            }
        }

        impl PartialOrd<Rational> for $T {
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
            let rat_num = self.0.inner_mut();
            let rat_den = self.1.inner_mut();
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

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Rational {
    type Output = mpq_t;
    fn inner(&self) -> &mpq_t {
        &self.inner
    }
}

impl InnerMut for Rational {
    unsafe fn inner_mut(&mut self) -> &mut mpq_t {
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
        assert_eq!(Rational::from(-&lhs), -lhs.clone());
        assert_eq!(Rational::from(&lhs + &rhs), lhs.clone() + &rhs);
        assert_eq!(Rational::from(&lhs - &rhs), lhs.clone() - &rhs);
        assert_eq!(Rational::from(&lhs * &rhs), lhs.clone() * &rhs);
        assert_eq!(Rational::from(&lhs / &rhs), lhs.clone() / &rhs);

        assert_eq!(Rational::from(&lhs << pu), lhs.clone() << pu);
        assert_eq!(Rational::from(&lhs >> pu), lhs.clone() >> pu);
        assert_eq!(Rational::from((&lhs).pow(pu)), lhs.clone().pow(pu));

        assert_eq!(Rational::from(&lhs << pi), lhs.clone() << pi);
        assert_eq!(Rational::from(&lhs >> pi), lhs.clone() >> pi);
        assert_eq!(Rational::from((&lhs).pow(pi)), lhs.clone().pow(pi));
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
                    let x = SmallRational::from((n, d));
                    println!("{}", *x);
                    println!("n {} d {} ans {:?}", n, d, ans);
                    println!("zero {}", zero);
                    println!("cmp() {:?}", zero.partial_cmp(&(n, d)));
                    println!("repeat");
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    println!("done");
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
        }
        for &n in &s {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
        }
    }

    #[test]
    fn check_from_str() {
        let bad_strings = [
            (" 1", None),
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
            ("9", Some(9)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Rational::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings = [
            ("0", 10, 0, 1),
            ("+0/fC", 16, 0, 1),
            ("-0/10", 2, 0, 1),
            ("-99/3", 10, -33, 1),
            ("+Ce/fF", 16, 0xce, 0xff),
            ("-77/2", 8, -0o77, 2),
        ];
        for &(s, radix, n, d) in good_strings.into_iter() {
            let r = Rational::from_str_radix(s, radix).unwrap();
            assert_eq!(*r.numer(), n);
            assert_eq!(*r.denom(), d);
        }
    }

    #[test]
    fn check_formatting() {
        let r = Rational::from((-11, 15));
        assert_eq!(format!("{}", r), "-11/15");
        assert_eq!(format!("{:?}", r), "-11/15");
        assert_eq!(format!("{:b}", r), "-1011/1111");
        assert_eq!(format!("{:#b}", r), "-0b1011/1111");
        assert_eq!(format!("{:o}", r), "-13/17");
        assert_eq!(format!("{:#o}", r), "-0o13/17");
        assert_eq!(format!("{:x}", r), "-b/f");
        assert_eq!(format!("{:X}", r), "-B/F");
        assert_eq!(format!("{:8x}", r), "    -b/f");
        assert_eq!(format!("{:08X}", r), "-0000B/F");
        assert_eq!(format!("{:#08x}", r), "-0x00b/f");
        assert_eq!(format!("{:#8X}", r), "  -0xB/F");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
    }
}
