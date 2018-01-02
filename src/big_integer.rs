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
use cast::cast;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use inner::{Inner, InnerMut};
use misc;
use ops::AssignInto;
#[cfg(feature = "rand")]
use rand::RandState;
use std::{i32, u32};
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::os::raw::{c_char, c_int, c_long};
use std::slice;

/// An arbitrary-precision integer.
///
/// Standard arithmetic operations, bitwise operations and comparisons
/// are supported. In standard arithmetic operations such as addition,
/// you can mix `Integer` and primitive integer types; the result will
/// be an `Integer`.
///
/// Internally the integer is not stored using two’s-complement
/// representation, however, for bitwise operations and shifts, the
/// functionality is the same as if the representation was using two’s
/// complement.
///
/// # Examples
///
/// ```rust
/// use rug::{Assign, Integer};
/// // Create an integer initialized as zero.
/// let mut int = Integer::new();
/// assert_eq!(int, 0);
/// assert_eq!(int.to_u32(), Some(0));
/// int.assign(-14);
/// assert_eq!(int, -14);
/// assert_eq!(int.to_u32(), None);
/// assert_eq!(int.to_i32(), Some(-14));
/// ```
///
/// Arithmetic operations with mixed arbitrary and primitive types are
/// allowed. Note that in the following example, there is only one
/// allocation. The `Integer` instance is moved into the shift
/// operation so that the result can be stored in the same instance,
/// then that result is similarly consumed by the addition operation.
///
/// ```rust
/// use rug::Integer;
/// let mut a = Integer::from(0xc);
/// a = (a << 80) + 0xffee;
/// assert_eq!(a.to_string_radix(16), "c0000000000000000ffee");
/// //                                  ^   ^   ^   ^   ^
/// //                                 80  64  48  32  16
/// ```
///
/// Bitwise operations on `Integer` values behave as if the value uses
/// two’s-complement representation.
///
/// ```rust
/// use rug::Integer;
///
/// let mut i = Integer::from(1);
/// i = i << 1000;
/// // i is now 1000000... (1000 zeros)
/// assert_eq!(i.significant_bits(), 1001);
/// assert_eq!(i.find_one(0), Some(1000));
/// i -= 1;
/// // i is now 111111... (1000 ones)
/// assert_eq!(i.count_ones(), Some(1000));
///
/// let a = Integer::from(0xf00d);
/// let all_ones_xor_a = Integer::from(-1) ^ &a;
/// // a is unchanged as we borrowed it
/// let complement_a = !a;
/// // now a has been moved, so this would cause an error:
/// // assert!(a > 0);
/// assert_eq!(all_ones_xor_a, complement_a);
/// assert_eq!(complement_a, -0xf00e);
/// assert_eq!(format!("{:x}", complement_a), "-f00e");
/// ```
///
/// To initialize a large `Integer` that does not fit in a primitive
/// type, you can parse a string.
///
/// ```rust
/// use rug::Integer;
/// let s1 = "123456789012345678901234567890";
/// let i1 = s1.parse::<Integer>().unwrap();
/// assert_eq!(i1.significant_bits(), 97);
/// let s2 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
/// let i2 = Integer::from_str_radix(s2, 16).unwrap();
/// assert_eq!(i2.significant_bits(), 160);
/// assert_eq!(i2.count_ones(), Some(80));
/// ```
///
/// Operations on two borrowed `Integer` values result in an
/// intermediate value that has to be assigned to a new `Integer`
/// value.
///
/// ```rust
/// use rug::Integer;
/// let a = Integer::from(10);
/// let b = Integer::from(3);
/// let a_b_ref = &a + &b;
/// let a_b = Integer::from(a_b_ref);
/// assert_eq!(a_b, 13);
/// ```
///
/// As a special case, when an intermediate value is obtained from
/// multiplying two `Integer` references, it can be added to or
/// subtracted from another `Integer` (or reference). This can be
/// useful for multiply-accumulate operations.
///
/// ```rust
/// use rug::Integer;
/// let mut acc = Integer::from(100);
/// let m1 = Integer::from(3);
/// let m2 = Integer::from(7);
/// // 100 + 3 * 7 = 121
/// acc += &m1 * &m2;
/// assert_eq!(acc, 121);
/// let other = Integer::from(2000);
/// // Do not consume any values here:
/// // 2000 - 3 * 7 = 1979
/// let sub = Integer::from(&other - &m1 * &m2);
/// assert_eq!(sub, 1979);
/// ```
///
/// The `Integer` type supports various functions. Most methods have
/// three versions: one that consumes the operand, one that mutates
/// the operand, and one that borrows the operand.
///
/// ```rust
/// use rug::Integer;
///
/// // 1. consume the operand
/// let a = Integer::from(-15);
/// let abs_a = a.abs();
/// assert_eq!(abs_a, 15);
///
/// // 2. mutate the operand
/// let mut b = Integer::from(-16);
/// b.abs_mut();
/// assert_eq!(b, 16);
///
/// // 3. borrow the operand
/// let c = Integer::from(-17);
/// let r = c.abs_ref();
/// let abs_c = Integer::from(r);
/// assert_eq!(abs_c, 17);
/// // c was not consumed
/// assert_eq!(c, -17);
/// ```
pub struct Integer {
    inner: mpz_t,
}

impl Integer {
    /// Constructs a new arbitrary-precision integer with value 0.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::new();
    /// assert_eq!(i, 0);
    /// ```
    #[inline]
    pub fn new() -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init(ret.inner_mut());
            ret
        }
    }

    /// Constructs a new arbitrary-precision integer with at least the
    /// specified capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::with_capacity(137);
    /// assert!(i.capacity() >= 137);
    /// ```
    #[inline]
    pub fn with_capacity(bits: usize) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init2(ret.inner_mut(), cast(bits));
            ret
        }
    }

    /// Returns the capacity in bits that can be stored without reallocating.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::with_capacity(137);
    /// assert!(i.capacity() >= 137);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        let bits = cast::<_, usize>(self.inner().alloc)
            .checked_mul(cast::<_, usize>(gmp::LIMB_BITS))
            .expect("overflow");
        bits
    }

    /// Reserves capacity for at least `additional` more bits in the
    /// `Integer`.
    ///
    /// If the integer already has enough excess capacity, this
    /// function does nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 0x2000_0000 needs 30 bits.
    /// let mut i = Integer::from(0x2000_0000);
    /// i.reserve(34);
    /// let capacity = i.capacity();
    /// assert!(capacity >= 64);
    /// i.reserve(34);
    /// assert!(i.capacity() == capacity);
    /// i.reserve(35);
    /// assert!(i.capacity() >= 65);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        if additional == 0 {
            return;
        }
        let used_bits = significant_bits_usize(self);
        let req_bits = used_bits.checked_add(additional).expect("overflow");
        unsafe {
            gmp::mpz_realloc2(self.inner_mut(), cast(req_bits));
        }
    }

    /// Shrinks the capacity of the `Integer` as much as possible.
    ///
    /// The capacity can still be larger than the number of
    /// significant bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// // let i be 100 bits wide
    /// let mut i = Integer::from_str_radix("fffff12345678901234567890", 16)
    ///     .unwrap();
    /// assert!(i.capacity() >= 100);
    /// i >>= 80;
    /// i.shrink_to_fit();
    /// assert!(i.capacity() >= 20);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let used_bits = significant_bits_usize(self);
        unsafe {
            gmp::mpz_realloc2(self.inner_mut(), cast(used_bits));
        }
    }

    /// Creates an `Integer` from an `f32` if it is finite, rounding
    /// towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::f32;
    /// let i = Integer::from_f32(-5.6).unwrap();
    /// assert_eq!(i, -5);
    /// let neg_inf = Integer::from_f32(f32::NEG_INFINITY);
    /// assert!(neg_inf.is_none());
    /// ```
    #[inline]
    pub fn from_f32(val: f32) -> Option<Integer> {
        Integer::from_f64(val.into())
    }

    /// Creates an `Integer` from an `f64` if it is finite, rounding
    /// towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::f64;
    /// let i = Integer::from_f64(1e20).unwrap();
    /// assert_eq!(i, "100000000000000000000".parse::<Integer>().unwrap());
    /// let inf = Integer::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    #[inline]
    pub fn from_f64(val: f64) -> Option<Integer> {
        if val.is_finite() {
            unsafe {
                let mut i: Integer = mem::uninitialized();
                gmp::mpz_init_set_d(i.inner_mut(), val);
                Some(i)
            }
        } else {
            None
        }
    }

    /// Parses an `Integer` using the given radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from_str_radix("-ff", 16).unwrap();
    /// assert_eq!(i, -0xff);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<Integer, ParseIntegerError> {
        let mut i = Integer::new();
        i.assign_str_radix(src, radix)?;
        Ok(i)
    }

    /// Checks if an `Integer` can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses an `Integer`. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// The string can start with an optional minus or plus sign.
    /// Whitespace is not allowed anywhere in the string, including in
    /// the beginning and end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    ///
    /// let valid1 = Integer::valid_str_radix("1223", 4);
    /// let i1 = Integer::from(valid1.unwrap());
    /// assert_eq!(i1, 3 + 4 * (2 + 4 * (2 + 4 * 1)));
    /// let valid2 = Integer::valid_str_radix("12yz", 36);
    /// let i2 = Integer::from(valid2.unwrap());
    /// assert_eq!(i2, 35 + 36 * (34 + 36 * (2 + 36 * 1)));
    ///
    /// let invalid = Integer::valid_str_radix("123", 3);
    /// let invalid_f = Integer::from_str_radix("123", 3);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidInteger, ParseIntegerError> {
        use self::ParseErrorKind as Kind;
        use self::ParseIntegerError as Error;

        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let bytes = src.as_bytes();
        let (skip_plus, iter) = match bytes.get(0) {
            Some(&b'+') => (&bytes[1..], bytes[1..].iter()),
            Some(&b'-') => (bytes, bytes[1..].iter()),
            _ => (bytes, bytes.iter()),
        };
        let mut got_digit = false;
        for b in iter {
            let digit_value = match *b {
                b'0'...b'9' => *b - b'0',
                b'a'...b'z' => *b - b'a' + 10,
                b'A'...b'Z' => *b - b'A' + 10,
                _ => {
                    return Err(Error {
                        kind: Kind::InvalidDigit,
                    })
                }
            };
            if digit_value >= cast::<_, u8>(radix) {
                return Err(Error {
                    kind: Kind::InvalidDigit,
                });
            }
            got_digit = true;
        }
        if !got_digit {
            return Err(Error {
                kind: Kind::NoDigits,
            });
        }
        let v = ValidInteger {
            bytes: skip_plus,
            radix,
        };
        Ok(v)
    }

    /// Converts to an `i8` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(-100);
    /// assert_eq!(fits.to_i8(), Some(-100));
    /// let small = Integer::from(-200);
    /// assert_eq!(small.to_i8(), None);
    /// let large = Integer::from(200);
    /// assert_eq!(large.to_i8(), None);
    /// ```
    #[inline]
    pub fn to_i8(&self) -> Option<i8> {
        if unsafe { xgmp::mpz_fits_i8(self.inner()) } {
            Some(self.to_i8_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `i16` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(-30_000);
    /// assert_eq!(fits.to_i16(), Some(-30_000));
    /// let small = Integer::from(-40_000);
    /// assert_eq!(small.to_i16(), None);
    /// let large = Integer::from(40_000);
    /// assert_eq!(large.to_i16(), None);
    /// ```
    #[inline]
    pub fn to_i16(&self) -> Option<i16> {
        if unsafe { xgmp::mpz_fits_i16(self.inner()) } {
            Some(self.to_i16_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `i32` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(-50);
    /// assert_eq!(fits.to_i32(), Some(-50));
    /// let small = Integer::from(-123456789012345_i64);
    /// assert_eq!(small.to_i32(), None);
    /// let large = Integer::from(123456789012345_i64);
    /// assert_eq!(large.to_i32(), None);
    /// ```
    #[inline]
    pub fn to_i32(&self) -> Option<i32> {
        if unsafe { xgmp::mpz_fits_i32(self.inner()) } {
            Some(self.to_i32_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `i64` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(-50);
    /// assert_eq!(fits.to_i64(), Some(-50));
    /// let small = Integer::from_str_radix("-fedcba9876543210", 16).unwrap();
    /// assert_eq!(small.to_i64(), None);
    /// let large = Integer::from_str_radix("fedcba9876543210", 16).unwrap();
    /// assert_eq!(large.to_i64(), None);
    /// ```
    #[inline]
    pub fn to_i64(&self) -> Option<i64> {
        if unsafe { xgmp::mpz_fits_i64(self.inner()) } {
            Some(self.to_i64_wrapping())
        } else {
            None
        }
    }

    /// Converts to an `isize` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(0x1000);
    /// assert_eq!(fits.to_isize(), Some(0x1000));
    /// let large: Integer = Integer::from(0x1000) << 128;
    /// assert_eq!(large.to_isize(), None);
    /// ```
    #[inline]
    pub fn to_isize(&self) -> Option<isize> {
        #[cfg(target_pointer_width = "32")]
        {
            self.to_i32().map(cast)
        }
        #[cfg(target_pointer_width = "64")]
        {
            self.to_i64().map(cast)
        }
    }

    /// Converts to a `u8` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(200);
    /// assert_eq!(fits.to_u8(), Some(200));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u8(), None);
    /// let large = Integer::from(300);
    /// assert_eq!(large.to_u8(), None);
    /// ```
    #[inline]
    pub fn to_u8(&self) -> Option<u8> {
        if unsafe { xgmp::mpz_fits_u8(self.inner()) } {
            Some(self.to_u8_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `u16` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(60_000);
    /// assert_eq!(fits.to_u16(), Some(60_000));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u16(), None);
    /// let large = Integer::from(70_000);
    /// assert_eq!(large.to_u16(), None);
    /// ```
    #[inline]
    pub fn to_u16(&self) -> Option<u16> {
        if unsafe { xgmp::mpz_fits_u16(self.inner()) } {
            Some(self.to_u16_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `u32` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(1234567890);
    /// assert_eq!(fits.to_u32(), Some(1234567890));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u32(), None);
    /// let large = Integer::from(123456789012345_u64);
    /// assert_eq!(large.to_u32(), None);
    /// ```
    #[inline]
    pub fn to_u32(&self) -> Option<u32> {
        if unsafe { xgmp::mpz_fits_u32(self.inner()) } {
            Some(self.to_u32_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `u64` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(123456789012345_u64);
    /// assert_eq!(fits.to_u64(), Some(123456789012345));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u64(), None);
    /// let large = "1234567890123456789012345".parse::<Integer>().unwrap();
    /// assert_eq!(large.to_u64(), None);
    /// ```
    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        if unsafe { xgmp::mpz_fits_u64(self.inner()) } {
            Some(self.to_u64_wrapping())
        } else {
            None
        }
    }

    /// Converts to a `usize` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(0x1000);
    /// assert_eq!(fits.to_usize(), Some(0x1000));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_usize(), None);
    /// let large: Integer = Integer::from(0x1000) << 128;
    /// assert_eq!(large.to_usize(), None);
    /// ```
    #[inline]
    pub fn to_usize(&self) -> Option<usize> {
        #[cfg(target_pointer_width = "32")]
        {
            self.to_u32().map(cast)
        }
        #[cfg(target_pointer_width = "64")]
        {
            self.to_u64().map(cast)
        }
    }

    /// Converts to an `i8`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large = Integer::from(0x1234);
    /// assert_eq!(large.to_i8_wrapping(), 0x34);
    /// ```
    #[inline]
    pub fn to_i8_wrapping(&self) -> i8 {
        self.to_u8_wrapping() as i8
    }

    /// Converts to an `i16`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large = Integer::from(0x1234_5678);
    /// assert_eq!(large.to_i16_wrapping(), 0x5678);
    /// ```
    #[inline]
    pub fn to_i16_wrapping(&self) -> i16 {
        self.to_u16_wrapping() as i16
    }

    /// Converts to an `i32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large = Integer::from(0x1234_5678_9abc_def0_u64);
    /// assert_eq!(large.to_i32_wrapping(), 0x9abc_def0_u32 as i32);
    /// ```
    #[inline]
    pub fn to_i32_wrapping(&self) -> i32 {
        self.to_u32_wrapping() as i32
    }

    /// Converts to an `i64`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large = Integer::from_str_radix("f123456789abcdef0", 16).unwrap();
    /// assert_eq!(large.to_i64_wrapping(), 0x1234_5678_9abc_def0);
    /// ```
    #[inline]
    pub fn to_i64_wrapping(&self) -> i64 {
        self.to_u64_wrapping() as i64
    }

    /// Converts to an `isize`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large: Integer = (Integer::from(0x1000) << 128) | 0x1234;
    /// assert_eq!(large.to_isize_wrapping(), 0x1234);
    /// ```
    #[inline]
    pub fn to_isize_wrapping(&self) -> isize {
        self.to_usize_wrapping() as isize
    }

    /// Converts to a `u8`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u8_wrapping(), 0xff);
    /// let large = Integer::from(0x1234);
    /// assert_eq!(large.to_u8_wrapping(), 0x34);
    /// ```
    #[inline]
    pub fn to_u8_wrapping(&self) -> u8 {
        let u = unsafe { xgmp::mpz_get_abs_u32(self.inner()) as u8 };
        if self.cmp0() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to a `u16`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u16_wrapping(), 0xffff);
    /// let large = Integer::from(0x1234_5678);
    /// assert_eq!(large.to_u16_wrapping(), 0x5678);
    /// ```
    #[inline]
    pub fn to_u16_wrapping(&self) -> u16 {
        let u = unsafe { xgmp::mpz_get_abs_u32(self.inner()) as u16 };
        if self.cmp0() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to a `u32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u32_wrapping(), 0xffff_ffff);
    /// let large = Integer::from(0x1234_5678_9abc_def0_u64);
    /// assert_eq!(large.to_u32_wrapping(), 0x9abc_def0);
    /// ```
    #[inline]
    pub fn to_u32_wrapping(&self) -> u32 {
        let u = unsafe { xgmp::mpz_get_abs_u32(self.inner()) };
        if self.cmp0() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to a `u64`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u64_wrapping(), 0xffff_ffff_ffff_ffff);
    /// let large = Integer::from_str_radix("f123456789abcdef0", 16).unwrap();
    /// assert_eq!(large.to_u64_wrapping(), 0x1234_5678_9abc_def0);
    /// ```
    #[inline]
    pub fn to_u64_wrapping(&self) -> u64 {
        let u = unsafe { xgmp::mpz_get_abs_u64(self.inner()) };
        if self.cmp0() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
        }
    }

    /// Converts to a `usize`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let large: Integer = (Integer::from(0x1000) << 128) | 0x1234;
    /// assert_eq!(large.to_usize_wrapping(), 0x1234);
    /// ```
    #[inline]
    pub fn to_usize_wrapping(&self) -> usize {
        #[cfg(target_pointer_width = "32")]
        {
            cast(self.to_u32_wrapping())
        }
        #[cfg(target_pointer_width = "64")]
        {
            cast(self.to_u64_wrapping())
        }
    }

    /// Converts to an `f32`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::f32;
    /// let min = Integer::from_f32(f32::MIN).unwrap();
    /// let min_minus_one = min - 1u32;
    /// // min_minus_one is truncated to f32::MIN
    /// assert_eq!(min_minus_one.to_f32(), f32::MIN);
    /// let times_two = min_minus_one * 2u32;
    /// // times_two is too small
    /// assert_eq!(times_two.to_f32(), f32::NEG_INFINITY);
    /// ```
    #[inline]
    pub fn to_f32(&self) -> f32 {
        misc::trunc_f64_to_f32(self.to_f64())
    }

    /// Converts to an `f64`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::f64;
    ///
    /// // An `f64` has 53 bits of precision.
    /// let exact = 0x1f_ffff_ffff_ffff_u64;
    /// let i = Integer::from(exact);
    /// assert_eq!(i.to_f64(), exact as f64);
    ///
    /// // large has 56 ones
    /// let large = 0xff_ffff_ffff_ffff_u64;
    /// // trunc has 53 ones followed by 3 zeros
    /// let trunc = 0xff_ffff_ffff_fff8_u64;
    /// let j = Integer::from(large);
    /// assert_eq!(j.to_f64() as u64, trunc);
    ///
    /// let max = Integer::from_f64(f64::MAX).unwrap();
    /// let max_plus_one = max + 1u32;
    /// // max_plus_one is truncated to f64::MAX
    /// assert_eq!(max_plus_one.to_f64(), f64::MAX);
    /// let times_two = max_plus_one * 2u32;
    /// // times_two is too large
    /// assert_eq!(times_two.to_f64(), f64::INFINITY);
    /// ```
    #[inline]
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpz_get_d(self.inner()) }
    }

    /// Converts to an `f32` and an exponent, rounding towards zero.
    ///
    /// The returned `f32` is in the range 0.5 ≤ *x* < 1. If the value
    /// is zero, `(0.0, 0)` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let zero = Integer::new();
    /// let (d0, exp0) = zero.to_f32_exp();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let fifteen = Integer::from(15);
    /// let (d15, exp15) = fifteen.to_f32_exp();
    /// assert_eq!((d15, exp15), (15.0 / 16.0, 4));
    /// ```
    #[inline]
    pub fn to_f32_exp(&self) -> (f32, u32) {
        let (f, exp) = self.to_f64_exp();
        let trunc_f = misc::trunc_f64_to_f32(f);
        (trunc_f, exp)
    }

    /// Converts to an `f64` and an exponent, rounding towards zero.
    ///
    /// The returned `f64` is in the range 0.5 ≤ *x* < 1. If the value
    /// is zero, `(0.0, 0)` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let zero = Integer::new();
    /// let (d0, exp0) = zero.to_f64_exp();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let fifteen = Integer::from(15);
    /// let (d15, exp15) = fifteen.to_f64_exp();
    /// assert_eq!((d15, exp15), (15.0 / 16.0, 4));
    /// ```
    #[inline]
    pub fn to_f64_exp(&self) -> (f64, u32) {
        let mut exp: c_long = 0;
        let f = unsafe { gmp::mpz_get_d_2exp(&mut exp, self.inner()) };
        (f, cast(exp))
    }

    /// Returns a string representation of the number for the
    /// specified `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::new();
    /// assert_eq!(i.to_string_radix(10), "0");
    /// i.assign(-10);
    /// assert_eq!(i.to_string_radix(16), "-a");
    /// i.assign(0x1234cdef);
    /// assert_eq!(i.to_string_radix(4), "102031030313233");
    /// i.assign_str_radix("123456789aAbBcCdDeEfF", 16).unwrap();
    /// assert_eq!(i.to_string_radix(16), "123456789aabbccddeeff");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix(&self, radix: i32) -> String {
        let mut s = String::new();
        append_to_string(&mut s, self, radix, false);
        s
    }

    /// Assigns from an `f32` if it is finite, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::f32;
    /// let mut i = Integer::new();
    /// let ret = i.assign_f64(-12.7);
    /// assert!(ret.is_ok());
    /// assert_eq!(i, -12);
    /// let ret = i.assign_f32(f32::NAN);
    /// assert!(ret.is_err());
    /// assert_eq!(i, -12);
    /// ```
    #[inline]
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val.into())
    }

    /// Assigns from an `f64` if it is finite, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// let ret = i.assign_f64(12.7);
    /// assert!(ret.is_ok());
    /// assert_eq!(i, 12);
    /// let ret = i.assign_f64(1.0 / 0.0);
    /// assert!(ret.is_err());
    /// assert_eq!(i, 12);
    /// ```
    #[inline]
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

    /// Parses an `Integer` from a string in decimal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str("123").unwrap();
    /// assert_eq!(i, 123);
    /// let ret = i.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    #[inline]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseIntegerError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses an `Integer` from a string with the specified radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str_radix("ff", 16).unwrap();
    /// assert_eq!(i, 0xff);
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
    ) -> Result<(), ParseIntegerError> {
        self.assign(Integer::valid_str_radix(src, radix)?);
        Ok(())
    }

    /// Borrows a negated copy of the `Integer`.
    ///
    /// The returned object implements `Deref<Integer>`.
    ///
    /// This method performs a shallow copy and negates it, and
    /// negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(42);
    /// let neg_i = i.as_neg();
    /// assert_eq!(*neg_i, -42);
    /// // methods taking &self can be used on the returned object
    /// let reneg_i = neg_i.as_neg();
    /// assert_eq!(*reneg_i, 42);
    /// assert_eq!(*reneg_i, i);
    /// ```
    #[inline]
    pub fn as_neg(&self) -> BorrowInteger {
        let mut ret = BorrowInteger {
            inner: self.inner,
            phantom: PhantomData,
        };
        ret.inner.size = self.inner.size.checked_neg().expect("overflow");
        ret
    }

    /// Borrows an absolute copy of the `Integer`.
    ///
    /// The returned object implements `Deref<Integer>`.
    ///
    /// This method performs a shallow copy and possibly negates it,
    /// and negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(-42);
    /// let abs_i = i.as_abs();
    /// assert_eq!(*abs_i, 42);
    /// // methods taking &self can be used on the returned object
    /// let reabs_i = abs_i.as_abs();
    /// assert_eq!(*reabs_i, 42);
    /// assert_eq!(*reabs_i, *abs_i);
    /// ```
    #[inline]
    pub fn as_abs(&self) -> BorrowInteger {
        let mut ret = BorrowInteger {
            inner: self.inner,
            phantom: PhantomData,
        };
        ret.inner.size = self.inner.size.checked_abs().expect("overflow");
        ret
    }

    /// Returns `true` if the number is even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// assert!(!(Integer::from(13).is_even()));
    /// assert!(Integer::from(-14).is_even());
    /// ```
    #[inline]
    pub fn is_even(&self) -> bool {
        unsafe { gmp::mpz_even_p(self.inner()) != 0 }
    }

    /// Returns `true` if the number is odd.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// assert!(Integer::from(13).is_odd());
    /// assert!(!Integer::from(-14).is_odd());
    /// ```
    #[inline]
    pub fn is_odd(&self) -> bool {
        unsafe { gmp::mpz_odd_p(self.inner()) != 0 }
    }

    /// Returns `true` if the number is divisible by `divisor`. Unlike
    /// other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(230);
    /// assert!(i.is_divisible(&Integer::from(10)));
    /// assert!(!i.is_divisible(&Integer::from(100)));
    /// assert!(!i.is_divisible(&Integer::new()));
    /// ```
    #[inline]
    pub fn is_divisible(&self, divisor: &Integer) -> bool {
        unsafe { gmp::mpz_divisible_p(self.inner(), divisor.inner()) != 0 }
    }

    /// Returns `true` if the number is divisible by `divisor`. Unlike
    /// other division functions, `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(230);
    /// assert!(i.is_divisible_u(23));
    /// assert!(!i.is_divisible_u(100));
    /// assert!(!i.is_divisible_u(0));
    /// ```
    #[inline]
    pub fn is_divisible_u(&self, divisor: u32) -> bool {
        unsafe { gmp::mpz_divisible_ui_p(self.inner(), divisor.into()) != 0 }
    }

    /// Returns `true` if the number is divisible by 2<sup>*b*</sup>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(15 << 17);
    /// assert!(i.is_divisible_2pow(16));
    /// assert!(i.is_divisible_2pow(17));
    /// assert!(!i.is_divisible_2pow(18));
    /// ```
    #[inline]
    pub fn is_divisible_2pow(&self, b: u32) -> bool {
        unsafe { gmp::mpz_divisible_2exp_p(self.inner(), b.into()) != 0 }
    }

    /// Returns `true` if the number is congruent to *c* mod
    /// *divisor*, that is, if there exists a *q* such that `self` =
    /// *c* + *q* × *divisor*. Unlike other division functions,
    /// `divisor` can be zero.
    ///
    /// # Examples
    ///

    /// ```rust
    /// use rug::Integer;
    /// let n = Integer::from(105);
    /// let divisor = Integer::from(10);
    /// assert!(n.is_congruent(&Integer::from(5), &divisor));
    /// assert!(n.is_congruent(&Integer::from(25), &divisor));
    /// assert!(!n.is_congruent(&Integer::from(7), &divisor));
    /// // n is congruent to itself if divisor is 0
    /// assert!(n.is_congruent(&n, &Integer::from(0)));
    /// ```
    #[inline]
    pub fn is_congruent(&self, c: &Integer, divisor: &Integer) -> bool {
        unsafe {
            gmp::mpz_congruent_p(self.inner(), c.inner(), divisor.inner()) != 0
        }
    }

    /// Returns `true` if the number is congruent to *c* mod
    /// *divisor*, that is, if there exists a *q* such that `self` =
    /// *c* + *q* × *divisor*. Unlike other division functions,
    /// `divisor` can be zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let n = Integer::from(105);
    /// assert!(n.is_congruent_u(3335, 10));
    /// assert!(!n.is_congruent_u(107, 10));
    /// // n is congruent to itself if divisor is 0
    /// assert!(n.is_congruent_u(105, 0));
    /// ```
    #[inline]
    pub fn is_congruent_u(&self, c: u32, divisor: u32) -> bool {
        unsafe {
            gmp::mpz_congruent_ui_p(self.inner(), c.into(), divisor.into()) != 0
        }
    }

    /// Returns `true` if the number is congruent to *c* mod
    /// 2<sup>*b*</sup>, that is, if there exists a *q* such that
    /// `self` = *c* + *q* × 2<sup>*b*</sup>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let n = Integer::from(13 << 17 | 21);
    /// assert!(n.is_congruent_2pow(&Integer::from(7 << 17 | 21), 17));
    /// assert!(!n.is_congruent_2pow(&Integer::from(13 << 17 | 22), 17));
    /// ```
    #[inline]
    pub fn is_congruent_2pow(&self, c: &Integer, b: u32) -> bool {
        unsafe {
            gmp::mpz_congruent_2exp_p(self.inner(), c.inner(), b.into()) != 0
        }
    }

    /// Returns `true` if the number is a perfect power.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
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
    #[inline]
    pub fn is_perfect_power(&self) -> bool {
        unsafe { gmp::mpz_perfect_power_p(self.inner()) != 0 }
    }

    /// Returns `true` if the number is a perfect square.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(1);
    /// assert!(i.is_perfect_square());
    /// i.assign(9);
    /// assert!(i.is_perfect_square());
    /// i.assign(15);
    /// assert!(!i.is_perfect_square());
    /// ```
    #[inline]
    pub fn is_perfect_square(&self) -> bool {
        unsafe { gmp::mpz_perfect_square_p(self.inner()) != 0 }
    }

    /// Returns the same result as `self.cmp(&0)`, but is faster.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::cmp::Ordering;
    /// assert_eq!(Integer::from(-5).cmp0(), Ordering::Less);
    /// assert_eq!(Integer::from(0).cmp0(), Ordering::Equal);
    /// assert_eq!(Integer::from(5).cmp0(), Ordering::Greater);
    /// ```
    #[inline]
    pub fn cmp0(&self) -> Ordering {
        unsafe { gmp::mpz_sgn(self.inner()).cmp(&0) }
    }

    /// Compares the absolute values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use std::cmp::Ordering;
    /// let a = Integer::from(-10);
    /// let b = Integer::from(4);
    /// assert_eq!(a.cmp(&b), Ordering::Less);
    /// assert_eq!(a.cmp_abs(&b), Ordering::Greater);
    /// ```
    #[inline]
    pub fn cmp_abs(&self, other: &Integer) -> Ordering {
        unsafe { gmp::mpz_cmpabs(self.inner(), other.inner()).cmp(&0) }
    }

    /// Returns the number of bits required to represent the absolute
    /// value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    ///
    /// assert_eq!(Integer::from(0).significant_bits(), 0);
    /// assert_eq!(Integer::from(1).significant_bits(), 1);
    /// assert_eq!(Integer::from(-1).significant_bits(), 1);
    /// assert_eq!(Integer::from(4).significant_bits(), 3);
    /// assert_eq!(Integer::from(-4).significant_bits(), 3);
    /// assert_eq!(Integer::from(7).significant_bits(), 3);
    /// assert_eq!(Integer::from(-7).significant_bits(), 3);
    /// ```
    #[inline]
    pub fn significant_bits(&self) -> u32 {
        cast(significant_bits_usize(self))
    }

    /// Returns the number of one bits if the value ≥ 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// assert_eq!(Integer::from(0).count_ones(), Some(0));
    /// assert_eq!(Integer::from(15).count_ones(), Some(4));
    /// assert_eq!(Integer::from(-1).count_ones(), None);
    /// ```
    #[inline]
    pub fn count_ones(&self) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_popcount(self.inner()) })
    }

    /// Returns the number of zero bits if the value < 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// assert_eq!(Integer::from(0).count_zeros(), None);
    /// assert_eq!(Integer::from(1).count_zeros(), None);
    /// assert_eq!(Integer::from(-1).count_zeros(), Some(0));
    /// assert_eq!(Integer::from(-2).count_zeros(), Some(1));
    /// assert_eq!(Integer::from(-7).count_zeros(), Some(2));
    /// assert_eq!(Integer::from(-8).count_zeros(), Some(3));
    /// ```
    #[inline]
    pub fn count_zeros(&self) -> Option<u32> {
        bitcount_to_u32(unsafe { xgmp::mpz_zerocount(self.inner()) })
    }

    /// Returns the location of the first zero, starting at `start`.
    /// If the bit at location `start` is zero, returns `start`.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // -2 is ...11111110
    /// assert_eq!(Integer::from(-2).find_zero(0), Some(0));
    /// assert_eq!(Integer::from(-2).find_zero(1), None);
    /// // 15 is ...00001111
    /// assert_eq!(Integer::from(15).find_zero(0), Some(4));
    /// assert_eq!(Integer::from(15).find_zero(20), Some(20));
    #[inline]
    pub fn find_zero(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan0(self.inner(), start.into()) })
    }

    /// Returns the location of the first one, starting at `start`.
    /// If the bit at location `start` is one, returns `start`.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 1 is ...00000001
    /// assert_eq!(Integer::from(1).find_one(0), Some(0));
    /// assert_eq!(Integer::from(1).find_one(1), None);
    /// // -16 is ...11110000
    /// assert_eq!(Integer::from(-16).find_one(0), Some(4));
    /// assert_eq!(Integer::from(-16).find_one(20), Some(20));
    #[inline]
    pub fn find_one(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan1(self.inner(), start.into()) })
    }

    /// Sets the bit at location `index` to 1 if `val` is `true` or 0
    /// if `val` is `false`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(-1);
    /// assert_eq!(*i.set_bit(0, false), -2);
    /// i.assign(0xff);
    /// assert_eq!(*i.set_bit(11, true), 0x8ff);
    /// ```
    #[inline]
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
    /// use rug::Integer;
    /// let i = Integer::from(0b100101);
    /// assert!(i.get_bit(0));
    /// assert!(!i.get_bit(1));
    /// assert!(i.get_bit(5));
    /// let neg = Integer::from(-1);
    /// assert!(neg.get_bit(1000));
    /// ```
    #[inline]
    pub fn get_bit(&self, index: u32) -> bool {
        unsafe { gmp::mpz_tstbit(self.inner(), index.into()) != 0 }
    }

    /// Toggles the bit at location `index`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::from(0b100101);
    /// i.toggle_bit(5);
    /// assert_eq!(i, 0b101);
    /// ```
    #[inline]
    pub fn toggle_bit(&mut self, index: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_combit(self.inner_mut(), index.into());
        }
        self
    }

    /// Retuns the Hamming distance if the two numbers have the same
    /// sign.
    ///
    /// The Hamming distance is the number of different bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// assert_eq!(Integer::from(0).hamming_dist(&i), None);
    /// assert_eq!(Integer::from(-1).hamming_dist(&i), Some(0));
    /// // -1 is ...11111111 and -13 is ...11110011
    /// assert_eq!(Integer::from(-13).hamming_dist(&i), Some(2));
    /// ```
    #[inline]
    pub fn hamming_dist(&self, other: &Integer) -> Option<u32> {
        bitcount_to_u32(unsafe {
            gmp::mpz_hamdist(self.inner(), other.inner())
        })
    }

    math_op1! {
        gmp::mpz_abs;
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-100);
        /// let abs = i.abs();
        /// assert_eq!(abs, 100);
        /// ```
        fn abs();
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(-100);
        /// i.abs_mut();
        /// assert_eq!(i, 100);
        /// ```
        fn abs_mut;
        /// Computes the absolute value.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-100);
        /// let r = i.abs_ref();
        /// let abs = Integer::from(r);
        /// assert_eq!(abs, 100);
        /// assert_eq!(i, -100);
        /// ```
        fn abs_ref -> AbsRef;
    }
    math_op1! {
        xgmp::mpz_signum;
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-100);
        /// let signum = i.signum();
        /// assert_eq!(signum, -1);
        /// ```
        fn signum();
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(-100);
        /// i.signum_mut();
        /// assert_eq!(i, -1);
        /// ```
        fn signum_mut;
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-100);
        /// let r = i.signum_ref();
        /// let signum = Integer::from(r);
        /// assert_eq!(signum, -1);
        /// assert_eq!(i, -100);
        /// ```
        fn signum_ref -> SignumRef;
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let min = -10;
    /// let max = 10;
    /// let too_small = Integer::from(-100);
    /// let clamped1 = too_small.clamp(&min, &max);
    /// assert_eq!(clamped1, -10);
    /// let in_range = Integer::from(3);
    /// let clamped2 = in_range.clamp(&min, &max);
    /// assert_eq!(clamped2, 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    #[inline]
    pub fn clamp<'a, 'b, Min, Max>(
        mut self,
        min: &'a Min,
        max: &'b Max,
    ) -> Integer
    where
        Integer: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'b Max>,
    {
        self.clamp_mut(min, max);
        self
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let min = -10;
    /// let max = 10;
    /// let mut too_small = Integer::from(-100);
    /// too_small.clamp_mut(&min, &max);
    /// assert_eq!(too_small, -10);
    /// let mut in_range = Integer::from(3);
    /// in_range.clamp_mut(&min, &max);
    /// assert_eq!(in_range, 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    pub fn clamp_mut<'a, 'b, Min, Max>(&mut self, min: &'a Min, max: &'b Max)
    where
        Integer: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'b Max>,
    {
        if (&*self).lt(min) {
            self.assign(min);
            assert!(!(&*self).gt(max), "minimum larger than maximum");
        } else if (&*self).gt(max) {
            self.assign(max);
            assert!(!(&*self).lt(min), "minimum larger than maximum");
        }
    }

    /// Clamps the value within the specified bounds.
    ///
    /// The returned object implements
    /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let min = -10;
    /// let max = 10;
    /// let too_small = Integer::from(-100);
    /// let r1 = too_small.clamp_ref(&min, &max);
    /// let clamped1 = Integer::from(r1);
    /// assert_eq!(clamped1, -10);
    /// let in_range = Integer::from(3);
    /// let r2 = in_range.clamp_ref(&min, &max);
    /// let clamped2 = Integer::from(r2);
    /// assert_eq!(clamped2, 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    #[inline]
    pub fn clamp_ref<'a, Min, Max>(
        &'a self,
        min: &'a Min,
        max: &'a Max,
    ) -> ClampRef<'a, Min, Max>
    where
        Integer: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'a Max>,
    {
        ClampRef {
            ref_self: self,
            min,
            max,
        }
    }

    math_op1! {
        gmp::mpz_fdiv_r_2exp;
        /// Keeps the *n* least significant bits only.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-1);
        /// let keep_8 = i.keep_bits(8);
        /// assert_eq!(keep_8, 0xff);
        /// ```
        fn keep_bits(n: u32);
        /// Keeps the *n* least significant bits only.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(-1);
        /// i.keep_bits_mut(8);
        /// assert_eq!(i, 0xff);
        /// ```
        fn keep_bits_mut;
        /// Keeps the *n* least significant bits only.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-1);
        /// let r = i.keep_bits_ref(8);
        /// let eight_bits = Integer::from(r);
        /// assert_eq!(eight_bits, 0xff);
        /// ```
        fn keep_bits_ref -> KeepBitsRef;
    }
    math_op1! {
        xgmp::mpz_next_pow_of_two;
        /// Finds the next power of two, or 1 if the number ≤ 0.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(-3).next_power_of_two();
        /// assert_eq!(i, 1);
        /// let i = Integer::from(4).next_power_of_two();
        /// assert_eq!(i, 4);
        /// let i = Integer::from(7).next_power_of_two();
        /// assert_eq!(i, 8);
        /// ```
        fn next_power_of_two();
        /// Finds the next power of two, or 1 if the number ≤ 0.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(53);
        /// i.next_power_of_two_mut();
        /// assert_eq!(i, 64);
        /// ```
        fn next_power_of_two_mut;
        /// Finds the next power of two, or 1 if the number ≤ 0.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(53);
        /// let r = i.next_power_of_two_ref();
        /// let next = Integer::from(r);
        /// assert_eq!(next, 64);
        /// ```
        fn next_power_of_two_ref -> NextPowerTwoRef;
    }
    math_op2_2! {
        xgmp::mpz_tdiv_qr_check;
        /// Performs a division producing both the quotient and
        /// remainder.
        ///
        /// The remainder has the same sign as the dividend.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(-10);
        /// let (quotient, rem) = dividend.div_rem(divisor);
        /// assert_eq!(quotient, -2);
        /// assert_eq!(rem, 3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem(divisor);
        /// Performs a division producing both the quotient and
        /// remainder.
        ///
        /// The remainder has the same sign as the dividend.
        ///
        /// The quotient is stored in `self` and the remainder is
        /// stored in `divisor`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut dividend_quotient = Integer::from(-23);
        /// let mut divisor_rem = Integer::from(10);
        /// dividend_quotient.div_rem_mut(&mut divisor_rem);
        /// assert_eq!(dividend_quotient, -2);
        /// assert_eq!(divisor_rem, -3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_mut;
        /// Performs a division producing both the quotient and
        /// remainder.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// The remainder has the same sign as the dividend.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(-23);
        /// let divisor = Integer::from(-10);
        /// let r = dividend.div_rem_ref(&divisor);
        /// let (quotient, rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(quotient, 2);
        /// assert_eq!(rem, -3);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn div_rem_ref -> DivRemRef;
    }
    math_op2_2! {
        xgmp::mpz_cdiv_qr_check;
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded up.
        ///
        /// The sign of the remainder is the opposite of the divisor’s
        /// sign.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(-10);
        /// let (quotient, rem) = dividend.div_rem_ceil(divisor);
        /// assert_eq!(quotient, -2);
        /// assert_eq!(rem, 3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_ceil(divisor);
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded up.
        ///
        /// The sign of the remainder is the opposite of the divisor’s
        /// sign.
        ///
        /// The quotient is stored in `self` and the remainder is
        /// stored in `divisor`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut dividend_quotient = Integer::from(-23);
        /// let mut divisor_rem = Integer::from(10);
        /// dividend_quotient.div_rem_ceil_mut(&mut divisor_rem);
        /// assert_eq!(dividend_quotient, -2);
        /// assert_eq!(divisor_rem, -3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_ceil_mut;
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded up.
        ///
        /// The sign of the remainder is the opposite of the divisor’s
        /// sign.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(-23);
        /// let divisor = Integer::from(-10);
        /// let r = dividend.div_rem_ceil_ref(&divisor);
        /// let (quotient, rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(quotient, 3);
        /// assert_eq!(rem, 7);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn div_rem_ceil_ref -> DivRemCeilRef;
    }
    math_op2_2! {
        xgmp::mpz_fdiv_qr_check;
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded down.
        ///
        /// The remainder has the same sign as the divisor.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(-10);
        /// let (quotient, rem) = dividend.div_rem_floor(divisor);
        /// assert_eq!(quotient, -3);
        /// assert_eq!(rem, -7);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_floor(divisor);
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded down.
        ///
        /// The remainder has the same sign as the divisor.
        ///
        /// The quotient is stored in `self` and the remainder is
        /// stored in `divisor`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut dividend_quotient = Integer::from(-23);
        /// let mut divisor_rem = Integer::from(10);
        /// dividend_quotient.div_rem_floor_mut(&mut divisor_rem);
        /// assert_eq!(dividend_quotient, -3);
        /// assert_eq!(divisor_rem, 7);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_floor_mut;
        /// Performs a division producing both the quotient and
        /// remainder, with the quotient rounded down.
        ///
        /// The remainder has the same sign as the divisor.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(-23);
        /// let divisor = Integer::from(-10);
        /// let r = dividend.div_rem_floor_ref(&divisor);
        /// let (quotient, rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(quotient, 2);
        /// assert_eq!(rem, -3);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn div_rem_floor_ref -> DivRemFloorRef;
    }
    math_op2_2! {
        xgmp::mpz_ediv_qr_check;
        /// Performs Euclidean division producing both the quotient
        /// and remainder, with a positive remainder.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(-10);
        /// let (quotient, rem) = dividend.div_rem_euc(divisor);
        /// assert_eq!(quotient, -2);
        /// assert_eq!(rem, 3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_euc(divisor);
        /// Performs Euclidean division producing both the quotient
        /// and remainder, with a positive remainder.
        ///
        /// The quotient is stored in `self` and the remainder is
        /// stored in `divisor`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut dividend_quotient = Integer::from(-23);
        /// let mut divisor_rem = Integer::from(10);
        /// dividend_quotient.div_rem_euc_mut(&mut divisor_rem);
        /// assert_eq!(dividend_quotient, -3);
        /// assert_eq!(divisor_rem, 7);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_euc_mut;
        /// Performs Euclidan division producing both the quotient and
        /// remainder, with a positive remainder.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(-23);
        /// let divisor = Integer::from(-10);
        /// let r = dividend.div_rem_euc_ref(&divisor);
        /// let (quotient, rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(quotient, 3);
        /// assert_eq!(rem, 7);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn div_rem_euc_ref -> DivRemEucRef;
    }

    /// Returns the modulo, or the remainder of Euclidean division by
    /// a `u32`.
    ///
    /// The result is always zero or positive.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let pos = Integer::from(23);
    /// assert_eq!(pos.mod_u(1), 0);
    /// assert_eq!(pos.mod_u(10), 3);
    /// assert_eq!(pos.mod_u(100), 23);
    /// let neg = Integer::from(-23);
    /// assert_eq!(neg.mod_u(1), 0);
    /// assert_eq!(neg.mod_u(10), 7);
    /// assert_eq!(neg.mod_u(100), 77);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `modulo` is zero.
    #[inline]
    pub fn mod_u(&self, modulo: u32) -> u32 {
        assert_ne!(modulo, 0, "division by zero");
        unsafe { gmp::mpz_fdiv_ui(self.inner(), modulo.into()) as u32 }
    }

    math_op2! {
        xgmp::mpz_divexact_check;
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(12345 * 54321);
        /// let quotient = i.div_exact(&Integer::from(12345));
        /// assert_eq!(quotient, 54321);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_exact(divisor);
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(12345 * 54321);
        /// i.div_exact_mut(&Integer::from(12345));
        /// assert_eq!(i, 54321);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_exact_mut;
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(12345 * 54321);
        /// let divisor = Integer::from(12345);
        /// let r = i.div_exact_ref(&divisor);
        /// let quotient = Integer::from(r);
        /// assert_eq!(quotient, 54321);
        /// ```
        fn div_exact_ref -> DivExactRef;
    }
    math_op1! {
        xgmp::mpz_divexact_ui_check;
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(12345 * 54321);
        /// let q = i.div_exact_u(12345);
        /// assert_eq!(q, 54321);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_exact_u(divisor: u32);
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(12345 * 54321);
        /// i.div_exact_u_mut(12345);
        /// assert_eq!(i, 54321);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_exact_u_mut;
        /// Performs an exact division.
        ///
        /// This is much faster than normal division, but produces
        /// correct results only when the division is exact.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(12345 * 54321);
        /// let r = i.div_exact_u_ref(12345);
        /// assert_eq!(Integer::from(r), 54321);
        /// ```
        fn div_exact_u_ref -> DivExactURef;
    }

    /// Finds the inverse modulo `modulo` and returns `Ok(inverse)` if
    /// it exists, or `Err(unchanged)` if the inverse does not exist.
    ///
    /// The returned object implements
    /// [`AssignInto<Result<&mut Integer, &mut Integer>>`][at].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let n = Integer::from(2);
    /// // Modulo 4, 2 has no inverse: there is no x such that 2 * x = 1.
    /// let inv_mod_4 = match n.invert(&Integer::from(4)) {
    ///     Ok(_) => unreachable!(),
    ///     Err(unchanged) => unchanged,
    /// };
    /// // no inverse exists, so value is unchanged
    /// assert_eq!(inv_mod_4, 2);
    /// let n = inv_mod_4;
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// let inv_mod_5 = match n.invert(&Integer::from(5)) {
    ///     Ok(inverse) => inverse,
    ///     Err(_) => unreachable!(),
    /// };
    /// assert_eq!(inv_mod_5, 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `modulo` is zero.
    ///
    /// [at]: (../ops/trait.AssignInto.html)
    #[inline]
    pub fn invert(mut self, modulo: &Integer) -> Result<Integer, Integer> {
        if self.invert_mut(modulo) {
            Ok(self)
        } else {
            Err(self)
        }
    }

    /// Finds the inverse modulo `modulo` and returns `true` if an
    /// inverse exists.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut n = Integer::from(2);
    /// // Modulo 4, 2 has no inverse: there is no x such that 2 * x = 1.
    /// let exists_4 = n.invert_mut(&Integer::from(4));
    /// assert!(!exists_4);
    /// assert_eq!(n, 2);
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// let exists_5 = n.invert_mut(&Integer::from(5));
    /// assert!(exists_5);
    /// assert_eq!(n, 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `modulo` is zero.
    #[inline]
    pub fn invert_mut(&mut self, modulo: &Integer) -> bool {
        unsafe {
            xgmp::mpz_invert_check(
                self.inner_mut(),
                self.inner(),
                modulo.inner(),
            ) != 0
        }
    }

    /// Finds the inverse modulo `modulo` if an inverse exists.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let n = Integer::from(2);
    /// // Modulo 4, 2 has no inverse, there is no x such that 2 * x = 1.
    /// // For this conversion, if no inverse exists, the Integer
    /// // created is left unchanged as 0.
    /// let mut ans = Result::from(n.invert_ref(&Integer::from(4)));
    /// println!("a");
    /// match ans {
    ///     Ok(_) => unreachable!(),
    ///     Err(ref unchanged) => assert_eq!(*unchanged, 0),
    /// }
    /// println!("b");
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// ans.assign(n.invert_ref(&Integer::from(5)));
    /// println!("c");
    /// match ans {
    ///     Ok(ref inverse) => assert_eq!(*inverse, 3),
    ///     Err(_) => unreachable!(),
    /// };
    /// println!("d");
    /// ```
    #[inline]
    pub fn invert_ref<'a>(&'a self, modulo: &'a Integer) -> InvertRef<'a> {
        InvertRef {
            ref_self: self,
            modulo,
        }
    }

    /// Raises a number to the power of `exponent` modulo `modulo` and
    /// returns `Ok(power)` if an answer exists, or `Err(unchanged)`
    /// if it does not.
    ///
    /// If `exponent` is negative, then the number must have an
    /// inverse modulo `modulo` for an answer to exist.
    ///
    /// # Examples
    ///
    /// When the exponent is positive, an answer always exists.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 7 ^ 5 = 16807
    /// let n = Integer::from(7);
    /// let e = Integer::from(5);
    /// let m = Integer::from(1000);
    /// let power = match n.pow_mod(&e, &m) {
    ///     Ok(power) => power,
    ///     Err(_) => unreachable!(),
    /// };
    /// assert_eq!(power, 807);
    /// ```
    ///
    /// When the exponent is negative, an answer exists if an inverse
    /// exists.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// let n = Integer::from(7);
    /// let e = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let power = match n.pow_mod(&e, &m) {
    ///     Ok(power) => power,
    ///     Err(_) => unreachable!(),
    /// };
    /// assert_eq!(power, 943);
    /// ```
    #[inline]
    pub fn pow_mod(
        mut self,
        exponent: &Integer,
        modulo: &Integer,
    ) -> Result<Integer, Integer> {
        if self.pow_mod_mut(exponent, modulo) {
            Ok(self)
        } else {
            Err(self)
        }
    }

    /// Raises a number to the power of `exponent` modulo `modulo` and
    /// returns `true` if an answer exists.
    ///
    /// If `exponent` is negative, then the number must have an
    /// inverse modulo `modulo` for an answer to exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// // Modulo 1000, 2 has no inverse: there is no x such that 2 * x =  1.
    /// let mut n = Integer::from(2);
    /// let e = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let exists = n.pow_mod_mut(&e, &m);
    /// assert!(!exists);
    /// assert_eq!(n, 2);
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// n.assign(7);
    /// let exists = n.pow_mod_mut(&e, &m);
    /// assert!(exists);
    /// assert_eq!(n, 943);
    /// ```
    pub fn pow_mod_mut(
        &mut self,
        exponent: &Integer,
        modulo: &Integer,
    ) -> bool {
        let abs_pow;
        let pow_inner = if exponent.cmp0() == Ordering::Less {
            if !(self.invert_mut(modulo)) {
                return false;
            }
            abs_pow = exponent.as_neg();
            abs_pow.inner()
        } else {
            exponent.inner()
        };
        unsafe {
            gmp::mpz_powm(
                self.inner_mut(),
                self.inner(),
                pow_inner,
                modulo.inner(),
            );
        }
        true
    }

    /// Raises a number to the power of `exponent` modulo `modulo` if
    /// an answer exists.
    ///
    /// If `exponent` is negative, then the number must have an
    /// inverse modulo `modulo` for an answer to exist.
    ///
    /// The returned object implements
    /// [`AssignInto<Result<&mut Integer, &mut Integer>>`][at].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// // Modulo 1000, 2 has no inverse: there is no x such that 2 * x =  1.
    /// let two = Integer::from(2);
    /// let e = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let mut ans = Result::from(two.pow_mod_ref(&e, &m));
    /// match ans {
    ///     Ok(_) => unreachable!(),
    ///     Err(ref unchanged) => assert_eq!(*unchanged, 0),
    /// }
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// let seven = Integer::from(7);
    /// ans.assign(seven.pow_mod_ref(&e, &m));
    /// match ans {
    ///     Ok(ref power) => assert_eq!(*power, 943),
    ///     Err(_) => unreachable!(),
    /// }
    /// ```
    ///
    /// [at]: (../ops/trait.AssignInto.html)
    #[inline]
    pub fn pow_mod_ref<'a>(
        &'a self,
        exponent: &'a Integer,
        modulo: &'a Integer,
    ) -> PowModRef<'a> {
        PowModRef {
            ref_self: self,
            exponent,
            modulo,
        }
    }

    math_op0! {
        /// Raises `base` to the power of `exponent`.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let p = Integer::u_pow_u(13, 12);
        /// let i = Integer::from(p);
        /// assert_eq!(i, 13_u64.pow(12));
        /// ```
        fn u_pow_u(base: u32, exponent: u32) -> UPowU;
    }

    /// Raises `base` to the power of `exponent`.
    #[deprecated(since = "0.9.2",
                 note = "use `u_pow_u` instead; \
                         `i.assign_u_pow_u(base, exponent)` can be replaced \
                         with `i.assign(Integer::u_pow_u(base, exponent)`.")]
    #[inline]
    pub fn assign_u_pow_u(&mut self, base: u32, exponent: u32) {
        Integer::u_pow_u(base, exponent).assign_into(self);
    }

    math_op0! {
        /// Raises `base` to the power of `exponent`.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let p = Integer::i_pow_u(-13, 13);
        /// let i = Integer::from(p);
        /// assert_eq!(i, (-13_i64).pow(13));
        /// ```
        fn i_pow_u(base: i32, exponent: u32) -> IPowU;
    }

    /// Raises `base` to the power of `exponent`.
    #[deprecated(since = "0.9.2",
                 note = "use `i_pow_u` instead; \
                         `i.assign_i_pow_u(base, exponent)` can be replaced \
                         with `i.assign(Integer::i_pow_u(base, exponent)`.")]
    #[inline]
    pub fn assign_i_pow_u(&mut self, base: i32, exponent: u32) {
        Integer::i_pow_u(base, exponent).assign_into(self);
    }

    math_op1! {
        xgmp::mpz_root_check;
        /// Computes the <i>n</i>th root and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(1004);
        /// let root = i.root(3);
        /// assert_eq!(root, 10);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if *n* is even and the value is negative.
        fn root(n: u32);
        /// Computes the <i>n</i>th root and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(1004);
        /// i.root_mut(3);
        /// assert_eq!(i, 10);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if *n* is even and the value is negative.
        fn root_mut;
        /// Computes the <i>n</i>th root and truncates the result.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(1004);
        /// assert_eq!(Integer::from(i.root_ref(3)), 10);
        /// ```
        fn root_ref -> RootRef;
    }
    math_op1_2! {
        xgmp::mpz_rootrem_check;
        /// Computes the <i>n</i>th root and returns the truncated
        /// root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root raised to the power of *n*.
        ///
        /// The initial value of `remainder` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(1004);
        /// let (root, rem) = i.root_rem(Integer::new(), 3);
        /// assert_eq!(root, 10);
        /// assert_eq!(rem, 4);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if *n* is even and the value is negative.
        fn root_rem(remainder, n: u32);
        /// Computes the <i>n</i>th root and returns the truncated
        /// root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root raised to the power of *n*.
        ///
        /// The initial value of `remainder` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(1004);
        /// let mut rem = Integer::new();
        /// i.root_rem_mut(&mut rem, 3);
        /// assert_eq!(i, 10);
        /// assert_eq!(rem, 4);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if *n* is even and the value is negative.
        fn root_rem_mut;
        /// Computes the <i>n</i>th root and returns the truncated
        /// root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root raised to the power of *n*.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let i = Integer::from(1004);
        /// let r = i.root_rem_ref(3);
        /// let mut root = Integer::new();
        /// let mut rem = Integer::new();
        /// (&mut root, &mut rem).assign(r);
        /// assert_eq!(root, 10);
        /// assert_eq!(rem, 4);
        /// let (other_root, other_rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(other_root, 10);
        /// assert_eq!(other_rem, 4);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn root_rem_ref -> RootRemRef;
    }
    math_op1! {
        xgmp::mpz_sqrt_check;
        /// Computes the square root and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(104);
        /// let sqrt = i.sqrt();
        /// assert_eq!(sqrt, 10);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is negative.
        fn sqrt();
        /// Computes the square root and truncates the result.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(104);
        /// i.sqrt_mut();
        /// assert_eq!(i, 10);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is negative.
        fn sqrt_mut;
        /// Computes the square root and truncates the result.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(104);
        /// assert_eq!(Integer::from(i.sqrt_ref()), 10);
        /// ```
        fn sqrt_ref -> SqrtRef;
    }
    math_op1_2! {
        xgmp::mpz_sqrtrem_check;
        /// Computes the square root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root squared.
        ///
        /// The initial value of `remainder` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(104);
        /// let (sqrt, rem) = i.sqrt_rem(Integer::new());
        /// assert_eq!(sqrt, 10);
        /// assert_eq!(rem, 4);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is negative.
        fn sqrt_rem(remainder);
        /// Computes the square root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root squared.
        ///
        /// The initial value of `remainder` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(104);
        /// let mut rem = Integer::new();
        /// i.sqrt_rem_mut(&mut rem);
        /// assert_eq!(i, 10);
        /// assert_eq!(rem, 4);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is negative.
        fn sqrt_rem_mut;
        /// Computes the square root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root squared.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let i = Integer::from(104);
        /// let r = i.sqrt_rem_ref();
        /// let mut sqrt = Integer::new();
        /// let mut rem = Integer::new();
        /// (&mut sqrt, &mut rem).assign(r);
        /// assert_eq!(sqrt, 10);
        /// assert_eq!(rem, 4);
        /// let (other_sqrt, other_rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(other_sqrt, 10);
        /// assert_eq!(other_rem, 4);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn sqrt_rem_ref -> SqrtRemRef;
    }

    /// Determines wheter a number is prime using some trial
    /// divisions, then `reps` Miller-Rabin probabilistic primality
    /// tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::integer::IsPrime;
    /// let no = Integer::from(163 * 4003);
    /// assert_eq!(no.is_probably_prime(15), IsPrime::No);
    /// let yes = Integer::from(21_751);
    /// assert_eq!(yes.is_probably_prime(15), IsPrime::Yes);
    /// // 817_504_243 is actually a prime.
    /// let probably = Integer::from(817_504_243);
    /// assert_eq!(probably.is_probably_prime(15), IsPrime::Probably);
    /// ```
    #[inline]
    pub fn is_probably_prime(&self, reps: u32) -> IsPrime {
        let p = unsafe { gmp::mpz_probab_prime_p(self.inner(), cast(reps)) };
        match p {
            0 => IsPrime::No,
            1 => IsPrime::Probably,
            2 => IsPrime::Yes,
            _ => unreachable!(),
        }
    }

    math_op1! {
        gmp::mpz_nextprime;
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(800_000_000);
        /// let prime = i.next_prime();
        /// assert_eq!(prime, 800_000_011);
        /// ```
        fn next_prime();
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut i = Integer::from(800_000_000);
        /// i.next_prime_mut();
        /// assert_eq!(i, 800_000_011);
        /// ```
        fn next_prime_mut;
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let i = Integer::from(800_000_000);
        /// let r = i.next_prime_ref();
        /// let prime = Integer::from(r);
        /// assert_eq!(prime, 800_000_011);
        /// ```
        fn next_prime_ref -> NextPrimeRef;
    }
    math_op2! {
        gmp::mpz_gcd;
        /// Finds the greatest common divisor.
        ///
        /// The result is always positive except when both inputs are
        /// zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let a = Integer::new();
        /// let mut b = Integer::new();
        /// // gcd of 0, 0 is 0
        /// let gcd1 = a.gcd(&b);
        /// assert_eq!(gcd1, 0);
        /// b.assign(10);
        /// // gcd of 0, 10 is 10
        /// let gcd2 = gcd1.gcd(&b);
        /// assert_eq!(gcd2, 10);
        /// b.assign(25);
        /// // gcd of 10, 25 is 5
        /// let gcd3 = gcd2.gcd(&b);
        /// assert_eq!(gcd3, 5);
        /// ```
        fn gcd(other);
        /// Finds the greatest common divisor.
        ///
        /// The result is always positive except when both inputs are
        /// zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let mut a = Integer::new();
        /// let mut b = Integer::new();
        /// // gcd of 0, 0 is 0
        /// a.gcd_mut(&b);
        /// assert_eq!(a, 0);
        /// b.assign(10);
        /// // gcd of 0, 10 is 10
        /// a.gcd_mut(&b);
        /// assert_eq!(a, 10);
        /// b.assign(25);
        /// // gcd of 10, 25 is 5
        /// a.gcd_mut(&b);
        /// assert_eq!(a, 5);
        /// ```
        fn gcd_mut;
        /// Finds the greatest common divisor.
        ///
        /// The result is always positive except when both inputs are
        /// zero.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let a = Integer::from(100);
        /// let b = Integer::from(125);
        /// let r = a.gcd_ref(&b);
        /// // gcd of 100, 125 is 25
        /// assert_eq!(Integer::from(r), 25);
        /// ```
        fn gcd_ref -> GcdRef;
    }
    math_op2_3! {
        gmp::mpz_gcdext;
        /// Finds the greatest common divisor (GCD) of the two inputs
        /// (`self` and `other`), and two multiplication coefficients
        /// to obtain the GCD from the two inputs.
        ///
        /// The GCD is always positive except when both inputs are
        /// zero. If the inputs are *a* and *b*, the GCD is *g*, and
        /// the multiplication coefficients are *s* and *t*, then
        ///
        /// *a* × *s* + *b* × *t* = *g*
        ///
        /// The values *s* and *t* are chosen such that normally,
        /// |<i>s</i>| < |<i>b</i>| / (2<i>g</i>) and |<i>t</i>| <
        /// |<i>a</i>| / (2<i>g</i>), and these relations define *s*
        /// and *t* uniquely. There are a few exceptional cases:
        ///
        /// * If |<i>a</i>| = |<i>b</i>|, then *s* = 0, *t* = sgn(*b*).
        /// * Otherwise, if *b* = 0 or |<i>b</i>| = 2<i>g</i>, then
        ///   *s* = sgn(*a*), and if *a* = 0 or |<i>a</i>| =
        ///   2<i>g</i>, then *t* = sgn(*b*).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let a = Integer::from(4);
        /// let b = Integer::from(6);
        /// let (g, s, t) = a.gcd_coeffs(b, Integer::new());
        /// assert_eq!(g, 2);
        /// assert_eq!(s, -1);
        /// assert_eq!(t, 1);
        /// ```
        fn gcd_coeffs(other, rop);
        /// Finds the greatest common divisor (GCD) of the two inputs
        /// (`self` and `other`), and two multiplication coefficients
        /// to obtain the GCD from the two inputs.
        ///
        /// The GCD is stored in `self`, and the two multiplication
        /// coefficients are stored in `other` and `rop`.
        ///
        /// The GCD is always positive except when both inputs are
        /// zero. If the inputs are *a* and *b*, the GCD is *g*, and
        /// the multiplication coefficients are *s* and *t*, then
        ///
        /// *a* × *s* + *b* × *t* = *g*
        ///
        /// The values *s* and *t* are chosen such that normally,
        /// |<i>s</i>| < |<i>b</i>| / (2<i>g</i>) and |<i>t</i>| <
        /// |<i>a</i>| / (2<i>g</i>), and these relations define *s*
        /// and *t* uniquely. There are a few exceptional cases:
        ///
        /// * If |<i>a</i>| = |<i>b</i>|, then *s* = 0, *t* = sgn(*b*).
        /// * Otherwise, if *b* = 0 or |<i>b</i>| = 2<i>g</i>, then
        ///   *s* = sgn(*a*), and if *a* = 0 or |<i>a</i>| =
        ///   2<i>g</i>, then *t* = sgn(*b*).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut a_g = Integer::from(4);
        /// let mut b_s = Integer::from(6);
        /// let mut t = Integer::new();
        /// a_g.gcd_coeffs_mut(&mut b_s, &mut t);
        /// assert_eq!(a_g, 2);
        /// assert_eq!(b_s, -1);
        /// assert_eq!(t, 1);
        /// ```
        fn gcd_coeffs_mut;
        /// Finds the greatest common divisor (GCD) of the two inputs
        /// (`self` and `other`), and two multiplication coefficients
        /// to obtain the GCD from the two inputs.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer, &mut Integer)>`][at].
        ///
        /// The GCD is always positive except when both inputs are
        /// zero. If the inputs are *a* and *b*, the GCD is *g*, and
        /// the multiplication coefficients are *s* and *t*, then
        ///
        /// *a* × *s* + *b* × *t* = *g*
        ///
        /// The values *s* and *t* are chosen such that normally,
        /// |<i>s</i>| < |<i>b</i>| / (2<i>g</i>) and |<i>t</i>| <
        /// |<i>a</i>| / (2<i>g</i>), and these relations define *s*
        /// and *t* uniquely. There are a few exceptional cases:
        ///
        /// * If |<i>a</i>| = |<i>b</i>|, then *s* = 0, *t* = sgn(*b*).
        /// * Otherwise, if *b* = 0 or |<i>b</i>| = 2<i>g</i>, then
        ///   *s* = sgn(*a*), and if *a* = 0 or |<i>a</i>| =
        ///   2<i>g</i>, then *t* = sgn(*b*).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let a = Integer::from(4);
        /// let b = Integer::from(6);
        /// let r = a.gcd_coeffs_ref(&b);
        /// let mut g = Integer::new();
        /// let mut s = Integer::new();
        /// let mut t = Integer::new();
        /// (&mut g, &mut s, &mut t).assign(r);
        /// assert_eq!(a, 4);
        /// assert_eq!(b, 6);
        /// assert_eq!(g, 2);
        /// assert_eq!(s, -1);
        /// assert_eq!(t, 1);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn gcd_coeffs_ref -> GcdCoeffsRef;
    }
    math_op2! {
        gmp::mpz_lcm;
        /// Finds the least common multiple.
        ///
        /// The result is always positive except when one or both
        /// inputs are zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let a = Integer::from(10);
        /// let mut b = Integer::from(25);
        /// // lcm of 10, 25 is 50
        /// let lcm1 = a.lcm(&b);
        /// assert_eq!(lcm1, 50);
        /// b.assign(0);
        /// // lcm of 50, 0 is 0
        /// let lcm2 = lcm1.lcm(&b);
        /// assert_eq!(lcm2, 0);
        /// ```
        fn lcm(other);
        /// Finds the least common multiple.
        ///
        /// The result is always positive except when one or both
        /// inputs are zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let mut a = Integer::from(10);
        /// let mut b = Integer::from(25);
        /// // lcm of 10, 25 is 50
        /// a.lcm_mut(&b);
        /// assert_eq!(a, 50);
        /// b.assign(0);
        /// // lcm of 50, 0 is 0
        /// a.lcm_mut(&b);
        /// assert_eq!(a, 0);
        /// ```
        fn lcm_mut;
        /// Finds the least common multiple.
        ///
        /// The result is always positive except when one or both
        /// inputs are zero.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let a = Integer::from(100);
        /// let b = Integer::from(125);
        /// let r = a.lcm_ref(&b);
        /// // lcm of 100, 125 is 500
        /// assert_eq!(Integer::from(r), 500);
        /// ```
        fn lcm_ref -> LcmRef;
    }

    /// Calculates the Jacobi symbol (`self`/<i>n</i>).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let m = Integer::from(10);
    /// let mut n = Integer::from(13);
    /// assert_eq!(m.jacobi(&n), 1);
    /// n.assign(15);
    /// assert_eq!(m.jacobi(&n), 0);
    /// n.assign(17);
    /// assert_eq!(m.jacobi(&n), -1);
    /// ```
    #[inline]
    pub fn jacobi(&self, n: &Integer) -> i32 {
        unsafe { gmp::mpz_jacobi(self.inner(), n.inner()) as i32 }
    }

    /// Calculates the Legendre symbol (`self`/<i>p</i>).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let a = Integer::from(5);
    /// let mut p = Integer::from(7);
    /// assert_eq!(a.legendre(&p), -1);
    /// p.assign(11);
    /// assert_eq!(a.legendre(&p), 1);
    /// ```
    #[inline]
    pub fn legendre(&self, p: &Integer) -> i32 {
        unsafe { gmp::mpz_legendre(self.inner(), p.inner()) as i32 }
    }

    /// Calculates the Jacobi symbol (`self`/<i>n</i>) with the
    /// Kronecker extension.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let k = Integer::from(3);
    /// let mut n = Integer::from(16);
    /// assert_eq!(k.kronecker(&n), 1);
    /// n.assign(17);
    /// assert_eq!(k.kronecker(&n), -1);
    /// n.assign(18);
    /// assert_eq!(k.kronecker(&n), 0);
    /// ```
    #[inline]
    pub fn kronecker(&self, n: &Integer) -> i32 {
        unsafe { gmp::mpz_kronecker(self.inner(), n.inner()) as i32 }
    }

    /// Removes all occurrences of `factor`, and returns the number of
    /// occurrences removed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::from(Integer::u_pow_u(13, 50));
    /// i *= 1000;
    /// let (remove, count) = i.remove_factor(&Integer::from(13));
    /// assert_eq!(remove, 1000);
    /// assert_eq!(count, 50);
    /// ```
    #[inline]
    pub fn remove_factor(mut self, factor: &Integer) -> (Integer, u32) {
        let count = self.remove_factor_mut(factor);
        (self, count)
    }

    /// Removes all occurrences of `factor`, and returns the number of
    /// occurrences removed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::from(Integer::u_pow_u(13, 50));
    /// i *= 1000;
    /// let count = i.remove_factor_mut(&Integer::from(13));
    /// assert_eq!(i, 1000);
    /// assert_eq!(count, 50);
    /// ```
    #[inline]
    pub fn remove_factor_mut(&mut self, factor: &Integer) -> u32 {
        let cnt = unsafe {
            gmp::mpz_remove(self.inner_mut(), self.inner(), factor.inner())
        };
        cast(cnt)
    }

    /// Removes all occurrences of `factor`, and counts the number of
    /// occurrences removed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(Integer::u_pow_u(13, 50));
    /// i *= 1000;
    /// let factor = Integer::from(13);
    /// let r = i.remove_factor_ref(&factor);
    /// let (mut j, mut count) = (Integer::new(), 0);
    /// (&mut j, &mut count).assign(r);
    /// assert_eq!(count, 50);
    /// assert_eq!(j, 1000);
    /// ```
    #[inline]
    pub fn remove_factor_ref<'a>(
        &'a self,
        factor: &'a Integer,
    ) -> RemoveFactorRef<'a> {
        RemoveFactorRef {
            ref_self: self,
            factor,
        }
    }

    math_op0! {
        /// Computes the factorial of *n*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
        /// let f = Integer::factorial(10);
        /// let i = Integer::from(f);
        /// assert_eq!(i, 3628800);
        /// ```
        fn factorial(n: u32) -> Factorial;
    }

    /// Computes the factorial of *n*.
    #[deprecated(since = "0.9.2",
                 note = "use `factorial` instead; `i.assign_factorial(n)` can \
                         be replaced with `i.assign(Integer::factorial(n))`.")]
    #[inline]
    pub fn assign_factorial(&mut self, n: u32) {
        Integer::factorial(n).assign_into(self);
    }

    math_op0! {
        /// Computes the double factorial of *n*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 10 * 8 * 6 * 4 * 2
        /// let f = Integer::factorial_2(10);
        /// let i = Integer::from(f);
        /// assert_eq!(i, 3840);
        /// ```
        fn factorial_2(n: u32) -> Factorial2;
    }

    /// Computes the double factorial of *n*.
    #[deprecated(since = "0.9.2",
                 note = "use `factorial_2` instead; `i.assign_factorial_2(n)` \
                         can be replaced with \
                         `i.assign(Integer::factorial_2(n))`.")]
    #[inline]
    pub fn assign_factorial_2(&mut self, n: u32) {
        Integer::factorial_2(n).assign_into(self);
    }

    math_op0! {
        /// Computes the *m*-multi factorial of *n*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 10 * 7 * 4 * 1
        /// let f = Integer::factorial_m(10, 3);
        /// let i = Integer::from(f);
        /// assert_eq!(i, 280);
        /// ```
        fn factorial_m(n: u32, m: u32) -> FactorialM;
    }

    /// Computes the *m*-multi factorial of *n*.
    #[deprecated(since = "0.9.2",
                 note = "use `factorial_m` instead; \
                         `i.assign_factorial_m(n, m)` can be replaced with \
                         `i.assign(Integer::factorial_m(n, m))`.")]
    #[inline]
    pub fn assign_factorial_m(&mut self, n: u32, m: u32) {
        Integer::factorial_m(n, m).assign_into(self);
    }

    math_op0! {
        /// Computes the primorial of *n*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 7 * 5 * 3 * 2
        /// let p = Integer::primorial(10);
        /// let i = Integer::from(p);
        /// assert_eq!(i, 210);
        /// ```
        #[inline]
        fn primorial(n: u32) -> Primorial;
    }

    /// Computes the primorial of *n*.
    #[deprecated(since = "0.9.2",
                 note = "use `primorial` instead; `i.assign_primorial(n)` can \
                         be replaced with `i.assign(Integer::primorial(n))`.")]
    #[inline]
    pub fn assign_primorial(&mut self, n: u32) {
        Integer::primorial(n).assign_into(self);
    }

    math_op1! {
        gmp::mpz_bin_ui;
        /// Computes the binomial coefficient over *k*.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 7 choose 2 is 21
        /// let i = Integer::from(7);
        /// let bin = i.binomial(2);
        /// assert_eq!(bin, 21);
        /// ```
        fn binomial(k: u32);
        /// Computes the binomial coefficient over *k*.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 7 choose 2 is 21
        /// let mut i = Integer::from(7);
        /// i.binomial_mut(2);
        /// assert_eq!(i, 21);
        /// ```
        fn binomial_mut;
        /// Computes the binomial coefficient over *k*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 7 choose 2 is 21
        /// let i = Integer::from(7);
        /// assert_eq!(Integer::from(i.binomial_ref(2)), 21);
        /// ```
        fn binomial_ref -> BinomialRef;
    }
    math_op0!{
        /// Computes the binomial coefficient *n* over *k*.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// // 7 choose 2 is 21
        /// let b = Integer::binomial_u(7, 2);
        /// let i = Integer::from(b);
        /// assert_eq!(i, 21);
        /// ```
        fn binomial_u(n: u32, k: u32) -> BinomialU;
    }

    /// Computes the binomial coefficient *n* over *k*.
    #[inline]
    #[deprecated(since = "0.9.2",
                 note = "use `binomial_u` instead; `i.assign_binomial_u(n, k)` \
                         can be replaced with \
                         `i.assign(Integer::binomial_u(n, k))`.")]
    pub fn assign_binomial_u(&mut self, n: u32, k: u32) {
        Integer::binomial_u(n, k).assign_into(self);
    }

    math_op0! {
        /// Computes the Fibonacci number.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// This function is meant for an isolated number. If a
        /// sequence of Fibonacci numbers is required, the first two
        /// values of the sequence should be computed with the
        /// [`fibonacci_2`](#method.fibonacci_2) method, then
        /// iterations should be used.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let f = Integer::fibonacci(12);
        /// let i = Integer::from(f);
        /// assert_eq!(i, 144);
        /// ```
        fn fibonacci(n: u32) -> Fibonacci;
    }

    /// Computes the Fibonacci number.
    #[inline]
    #[deprecated(since = "0.9.2",
                 note = "use `fibonacci` instead; `i.assign_fibonacci(n)` can \
                         be replaced with `i.assign(Integer::fibonacci(n))`.")]
    pub fn assign_fibonacci(&mut self, n: u32) {
        Integer::fibonacci(n).assign_into(self);
    }

    math_op0! {
        /// Computes a Fibonacci number, and the previous Fibonacci
        /// number.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// This function is meant to calculate isolated numbers. If a
        /// sequence of Fibonacci numbers is required, the first two
        /// values of the sequence should be computed with this function,
        /// then iterations should be used.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let f = Integer::fibonacci_2(12);
        /// let mut pair = <(Integer, Integer)>::from(f);
        /// assert_eq!(pair.0, 144);
        /// assert_eq!(pair.1, 89);
        /// // Fibonacci number F[-1] is 1
        /// pair.assign(Integer::fibonacci_2(0));
        /// assert_eq!(pair.0, 0);
        /// assert_eq!(pair.1, 1);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn fibonacci_2(n: u32) -> Fibonacci2;
    }

    /// Computes a Fibonacci number, and the previous Fibonacci number.
    #[deprecated(since = "0.9.2",
                 note = "use `fibonacci_2` instead; `i.assign_fibonacci_2(n)` \
                         can be replaced with \
                         `i.assign(Integer::fibonacci_2(n))`.")]
    #[inline]
    pub fn assign_fibonacci_2(&mut self, previous: &mut Integer, n: u32) {
        Integer::fibonacci_2(n).assign_into(&mut (self, previous));
    }

    math_op0! {
        /// Computes the Lucas number.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// This function is meant for an isolated number. If a
        /// sequence of Lucas numbers is required, the first two
        /// values of the sequence should be computed with the
        /// [`lucas_2`](#method.lucas_2) method, then iterations
        /// should be used.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let l = Integer::lucas(12);
        /// let i = Integer::from(l);
        /// assert_eq!(i, 322);
        /// ```
        fn lucas(n: u32) -> Lucas;
    }

    /// Computes the Lucas number.
    #[deprecated(since = "0.9.2",
                 note = "use `lucas` instead; `i.assign_lucas(n)` can be \
                         replaced with `i.assign(Integer::lucas(n))`.")]
    #[inline]
    pub fn assign_lucas(&mut self, n: u32) {
        Integer::lucas(n).assign_into(self);
    }

    math_op0! {
        /// Computes a Lucas number, and the previous Lucas number.
        ///
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Integer, &mut Integer)>`][at].
        ///
        /// This function is meant to calculate isolated numbers. If a
        /// sequence of Lucas numbers is required, the first two values of
        /// the sequence should be computed with this function, then
        /// iterations should be used.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer};
        /// let l = Integer::lucas_2(12);
        /// let mut pair = <(Integer, Integer)>::from(l);
        /// assert_eq!(pair.0, 322);
        /// assert_eq!(pair.1, 199);
        /// pair.assign(Integer::lucas_2(0));
        /// assert_eq!(pair.0, 2);
        /// assert_eq!(pair.1, -1);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn lucas_2(n: u32) -> Lucas2;
    }

    /// Computes a Lucas number, and the previous Lucas number.
    #[deprecated(since = "0.9.2",
                 note = "use `lucas_2` instead; `i.assign_lucas_2(n)` can be \
                         replaced with `i.assign(Integer::lucas_2(n))`.")]
    #[inline]
    pub fn assign_lucas_2(&mut self, previous: &mut Integer, n: u32) {
        Integer::lucas_2(n).assign_into(&mut (self, previous));
    }

    #[cfg(feature = "rand")]
    /// Generates a random number with a specified maximum number of
    /// bits.
    ///
    /// The returned object implements
    /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut i = Integer::from(Integer::random_bits(0, &mut rand));
    /// assert_eq!(i, 0);
    /// i.assign(Integer::random_bits(80, &mut rand));
    /// assert!(i.significant_bits() <= 80);
    /// ```
    #[inline]
    pub fn random_bits<'a, 'b: 'a>(
        bits: u32,
        rng: &'a mut RandState<'b>,
    ) -> RandomBits<'a, 'b> {
        RandomBits { bits, rng }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number with a specified maximum number of
    /// bits.
    #[inline]
    #[deprecated(since = "0.9.2",
                 note = "use `random_bits` instead; \
                         `i.assign_random_bits(bits, rng)` can be replaced \
                         with `i.assign(Integer::random_bits(bits, rng))`.")]
    pub fn assign_random_bits(&mut self, bits: u32, rng: &mut RandState) {
        Integer::random_bits(bits, rng).assign_into(self);
    }

    #[cfg(feature = "rand")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let i = Integer::from(15);
    /// let below = i.random_below(&mut rand);
    /// println!("0 ≤ {} < 15", below);
    /// assert!(below < 15);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[inline]
    pub fn random_below(mut self, rng: &mut RandState) -> Integer {
        self.random_below_mut(rng);
        self
    }

    #[cfg(feature = "rand")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut i = Integer::from(15);
    /// i.random_below_mut(&mut rand);
    /// println!("0 ≤ {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[inline]
    pub fn random_below_mut(&mut self, rng: &mut RandState) {
        assert_eq!(self.cmp0(), Ordering::Greater, "cannot be below zero");
        unsafe {
            gmp::mpz_urandomm(self.inner_mut(), rng.inner_mut(), self.inner());
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let bound = Integer::from(15);
    /// let i = Integer::from(bound.random_below_ref(&mut rand));
    /// println!("0 ≤ {} < {}", i, bound);
    /// assert!(i < bound);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[inline]
    pub fn random_below_ref<'a, 'b: 'a>(
        &'a self,
        rng: &'a mut RandState<'b>,
    ) -> RandomBelowRef<'a, 'b> {
        RandomBelowRef {
            ref_self: self,
            rng,
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[deprecated(since = "0.9.2",
                 note = "use `random_below_ref` instead; \
                         `i.assign_random_below(bound, rng)` can be replaced \
                         with `i.assign(bound.random_below_ref(rng))`.")]
    #[inline]
    pub fn assign_random_below<'a, 'b: 'a>(
        &mut self,
        bound: &'a Integer,
        rng: &'a mut RandState<'b>,
    ) {
        bound.random_below_ref(rng).assign_into(self);
    }
}

ref_math_op1! { Integer; gmp::mpz_abs; struct AbsRef {} }
ref_math_op1! { Integer; xgmp::mpz_signum; struct SignumRef {} }

#[derive(Clone, Copy)]
pub struct ClampRef<'a, Min, Max>
where
    Integer: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    ref_self: &'a Integer,
    min: &'a Min,
    max: &'a Max,
}

impl<'a, Min, Max> AssignInto<Integer> for ClampRef<'a, Min, Max>
where
    Integer: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        if self.ref_self.lt(self.min) {
            dst.assign(self.min);
            assert!(!(&*dst).gt(self.max), "minimum larger than maximum");
        } else if self.ref_self.gt(self.max) {
            dst.assign(self.max);
            assert!(!(&*dst).lt(self.min), "minimum larger than maximum");
        } else {
            dst.assign(self.ref_self);
        }
    }
}

impl<'a, Min, Max> From<ClampRef<'a, Min, Max>> for Integer
where
    Integer: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn from(src: ClampRef<'a, Min, Max>) -> Self {
        let mut dst = Integer::new();
        src.assign_into(&mut dst);
        dst
    }
}

ref_math_op1! { Integer; gmp::mpz_fdiv_r_2exp; struct KeepBitsRef { n: u32 } }
ref_math_op1! { Integer; xgmp::mpz_next_pow_of_two; struct NextPowerTwoRef {} }
ref_math_op2_2! {
    Integer; xgmp::mpz_tdiv_qr_check; struct DivRemRef { divisor }
}
ref_math_op2_2! {
    Integer; xgmp::mpz_cdiv_qr_check; struct DivRemCeilRef { divisor }
}
ref_math_op2_2! {
    Integer; xgmp::mpz_fdiv_qr_check; struct DivRemFloorRef { divisor }
}
ref_math_op2_2! {
    Integer; xgmp::mpz_ediv_qr_check; struct DivRemEucRef { divisor }
}
ref_math_op2! {
    Integer; xgmp::mpz_divexact_check; struct DivExactRef { divisor }
}
ref_math_op1! {
    Integer; xgmp::mpz_divexact_ui_check; struct DivExactURef { divisor: u32 }
}

#[derive(Clone, Copy)]
pub struct PowModRef<'a> {
    ref_self: &'a Integer,
    exponent: &'a Integer,
    modulo: &'a Integer,
}

impl<'a, 'b> AssignInto<Result<&'a mut Integer, &'a mut Integer>>
    for PowModRef<'b> {
    fn assign_into(self, dst: &mut Result<&'a mut Integer, &'a mut Integer>) {
        if self.exponent.cmp0() == Ordering::Less {
            self.ref_self.invert_ref(self.modulo).assign_into(dst);
            if let Ok(ref mut inv) = *dst {
                let abs_exp = self.exponent.as_neg();
                unsafe {
                    gmp::mpz_powm(
                        inv.inner_mut(),
                        inv.inner(),
                        abs_exp.inner(),
                        self.modulo.inner(),
                    );
                }
            }
        } else {
            if dst.is_err() {
                misc::result_swap(dst);
            }
            if let Ok(ref mut dest) = *dst {
                unsafe {
                    gmp::mpz_powm(
                        dest.inner_mut(),
                        self.ref_self.inner(),
                        self.exponent.inner(),
                        self.modulo.inner(),
                    );
                }
            }
        }
    }
}

impl<'a> From<PowModRef<'a>> for Result<Integer, Integer> {
    #[inline]
    fn from(src: PowModRef<'a>) -> Self {
        let mut dst = Ok(Integer::new());
        let is_err = {
            let mut m = dst.as_mut();
            src.assign_into(&mut m);
            m.is_err()
        };
        if is_err {
            misc::result_swap(&mut dst);
        }
        dst
    }
}

ref_math_op0! {
    Integer; gmp::mpz_ui_pow_ui; struct UPowU { base: u32, exponent: u32 }
}
ref_math_op0! {
    Integer; xgmp::mpz_si_pow_ui; struct IPowU { base: i32, exponent: u32 }
}
ref_math_op1! { Integer; xgmp::mpz_root_check; struct RootRef { n: u32 } }
ref_math_op1_2! {
    Integer; xgmp::mpz_rootrem_check; struct RootRemRef { n: u32 }
}
ref_math_op1! { Integer; xgmp::mpz_sqrt_check; struct SqrtRef {} }
ref_math_op1_2! { Integer; xgmp::mpz_sqrtrem_check; struct SqrtRemRef {} }
ref_math_op1! { Integer; gmp::mpz_nextprime; struct NextPrimeRef {} }
ref_math_op2! { Integer; gmp::mpz_gcd; struct GcdRef { other } }
ref_math_op2_3! { Integer; gmp::mpz_gcdext; struct GcdCoeffsRef { other } }
ref_math_op2! { Integer; gmp::mpz_lcm; struct LcmRef { other } }

#[derive(Clone, Copy)]
pub struct InvertRef<'a> {
    ref_self: &'a Integer,
    modulo: &'a Integer,
}

impl<'a, 'b> AssignInto<Result<&'a mut Integer, &'a mut Integer>>
    for InvertRef<'b> {
    fn assign_into(self, dst: &mut Result<&'a mut Integer, &'a mut Integer>) {
        let exists = {
            let dest = match *dst {
                Ok(ref mut i) | Err(ref mut i) => i,
            };
            unsafe {
                xgmp::mpz_invert_check(
                    dest.inner_mut(),
                    self.ref_self.inner(),
                    self.modulo.inner(),
                ) != 0
            }
        };
        if exists != dst.is_ok() {
            misc::result_swap(dst);
        }
    }
}

impl<'a> From<InvertRef<'a>> for Result<Integer, Integer> {
    #[inline]
    fn from(src: InvertRef<'a>) -> Self {
        let mut dst = Ok(Integer::new());
        let is_err = {
            let mut m = dst.as_mut();
            src.assign_into(&mut m);
            m.is_err()
        };
        if is_err {
            misc::result_swap(&mut dst);
        }
        dst
    }
}

#[derive(Clone, Copy)]
pub struct RemoveFactorRef<'a> {
    ref_self: &'a Integer,
    factor: &'a Integer,
}

impl<'a, 'b, 'c> AssignInto<(&'a mut Integer, &'b mut u32)>
    for RemoveFactorRef<'c> {
    #[inline]
    fn assign_into(self, dst: &mut (&'a mut Integer, &'b mut u32)) {
        let cnt = unsafe {
            gmp::mpz_remove(
                dst.0.inner_mut(),
                self.ref_self.inner(),
                self.factor.inner(),
            )
        };
        *dst.1 = cast(cnt);
    }
}

impl<'a> From<RemoveFactorRef<'a>> for (Integer, u32) {
    #[inline]
    fn from(src: RemoveFactorRef<'a>) -> Self {
        let mut dst = (Integer::new(), 0u32);
        src.assign_into(&mut (&mut dst.0, &mut dst.1));
        dst
    }
}

ref_math_op0! { Integer; gmp::mpz_fac_ui; struct Factorial { n: u32 } }
ref_math_op0! { Integer; gmp::mpz_2fac_ui; struct Factorial2 { n: u32 } }
ref_math_op0! {
    Integer; gmp::mpz_mfac_uiui; struct FactorialM { n: u32, m: u32 }
}
ref_math_op0! { Integer; gmp::mpz_primorial_ui; struct Primorial { n: u32 } }
ref_math_op1! { Integer; gmp::mpz_bin_ui; struct BinomialRef { k: u32 } }
ref_math_op0! {
    Integer; gmp::mpz_bin_uiui; struct BinomialU { n: u32, k: u32 }
}
ref_math_op0! { Integer; gmp::mpz_fib_ui; struct Fibonacci { n: u32 } }
ref_math_op0_2! { Integer; gmp::mpz_fib2_ui; struct Fibonacci2 { n: u32 } }
ref_math_op0! { Integer; gmp::mpz_lucnum_ui; struct Lucas { n: u32 } }
ref_math_op0_2! { Integer; gmp::mpz_lucnum2_ui; struct Lucas2 { n: u32 } }

#[cfg(feature = "rand")]
pub struct RandomBits<'a, 'b: 'a> {
    bits: u32,
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignInto<Integer> for RandomBits<'a, 'b> {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            gmp::mpz_urandomb(
                dst.inner_mut(),
                self.rng.inner_mut(),
                self.bits.into(),
            );
        }
    }
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> From<RandomBits<'a, 'b>> for Integer {
    #[inline]
    fn from(src: RandomBits<'a, 'b>) -> Self {
        let mut dst = Integer::new();
        src.assign_into(&mut dst);
        dst
    }
}

#[cfg(feature = "rand")]
pub struct RandomBelowRef<'a, 'b: 'a> {
    ref_self: &'a Integer,
    rng: &'a mut RandState<'b>,
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> AssignInto<Integer> for RandomBelowRef<'a, 'b> {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        assert_eq!(
            self.ref_self.cmp0(),
            Ordering::Greater,
            "cannot be below zero"
        );
        unsafe {
            gmp::mpz_urandomm(
                dst.inner_mut(),
                self.rng.inner_mut(),
                self.ref_self.inner(),
            );
        }
    }
}

#[cfg(feature = "rand")]
impl<'a, 'b: 'a> From<RandomBelowRef<'a, 'b>> for Integer {
    #[inline]
    fn from(src: RandomBelowRef<'a, 'b>) -> Self {
        let mut dst = Integer::new();
        src.assign_into(&mut dst);
        dst
    }
}

#[derive(Clone, Copy)]
pub struct BorrowInteger<'a> {
    inner: mpz_t,
    phantom: PhantomData<&'a Integer>,
}

impl<'a> Deref for BorrowInteger<'a> {
    type Target = Integer;
    #[inline]
    fn deref(&self) -> &Integer {
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

pub fn req_chars(i: &Integer, radix: i32, extra: usize) -> usize {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let size = unsafe { gmp::mpz_sizeinbase(i.inner(), radix) };
    let size_extra = size.checked_add(extra).expect("overflow");
    if i.cmp0() == Ordering::Less {
        size_extra.checked_add(1).expect("overflow")
    } else {
        size_extra
    }
}

pub fn append_to_string(
    s: &mut String,
    i: &Integer,
    radix: i32,
    to_upper: bool,
) {
    // add 1 for nul
    let size = req_chars(i, radix, 1);
    s.reserve(size);
    let case_radix = if to_upper { -radix } else { radix };
    let orig_len = s.len();
    unsafe {
        let bytes = s.as_mut_vec();
        let start = bytes.as_mut_ptr().offset(orig_len as isize);
        gmp::mpz_get_str(start as *mut c_char, case_radix as c_int, i.inner());
        let added = slice::from_raw_parts(start, size);
        let nul_index = added.iter().position(|&x| x == 0).unwrap();
        bytes.set_len(orig_len + nul_index);
    }
}

/// A validated string that can always be converted to an
/// [`Integer`](../struct.Integer.html).
///
/// See the [`Integer::valid_str_radix`][valid] method.
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::integer::ValidInteger;
/// // This string is correct in radix 10, it cannot fail.
/// let s = "12345";
/// let valid: ValidInteger = match Integer::valid_str_radix(s, 10) {
///     Ok(valid) => valid,
///     Err(_) => unreachable!(),
/// };
/// let i = Integer::from(valid);
/// assert_eq!(i, 12345);
/// ```
///
/// [valid]: ../struct.Integer.html#method.valid_str_radix
#[derive(Clone, Debug)]
pub struct ValidInteger<'a> {
    bytes: &'a [u8],
    radix: i32,
}

impl<'a> AssignInto<Integer> for ValidInteger<'a> {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        let mut v = Vec::<u8>::with_capacity(self.bytes.len() + 1);
        v.extend_from_slice(self.bytes);
        v.push(0);
        let err = unsafe {
            let c_str = CStr::from_bytes_with_nul_unchecked(&v);
            gmp::mpz_set_str(dst.inner_mut(), c_str.as_ptr(), self.radix.into())
        };
        assert_eq!(err, 0);
    }
}

impl<'a> From<ValidInteger<'a>> for Integer {
    #[inline]
    fn from(src: ValidInteger<'a>) -> Self {
        let mut dst = Integer::new();
        src.assign_into(&mut dst);
        dst
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing an `Integer`.
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::integer::ParseIntegerError;
/// // This string is not an integer.
/// let s = "something completely different (_!_!_)";
/// let error: ParseIntegerError = match Integer::valid_str_radix(s, 4) {
///     Ok(_) => unreachable!(),
///     Err(error) => error,
/// };
/// println!("Parse error: {:?}", error);
/// ```
pub struct ParseIntegerError {
    kind: ParseErrorKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// Whether a number is prime.
///
/// See the [`Integer::is_probably_prime`][ipp] method.
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::integer::IsPrime;
/// let no = Integer::from(163 * 4003);
/// assert_eq!(no.is_probably_prime(15), IsPrime::No);
/// let yes = Integer::from(21_751);
/// assert_eq!(yes.is_probably_prime(15), IsPrime::Yes);
/// // 817_504_243 is actually a prime.
/// let probably = Integer::from(817_504_243);
/// assert_eq!(probably.is_probably_prime(15), IsPrime::Probably);
/// ```
///
/// [ipp]: ../struct.Integer.html#method.is_probably_prime
pub enum IsPrime {
    /// The number is definitely not prime.
    No,
    /// The number is probably prime.
    Probably,
    /// The number is definitely prime.
    Yes,
}

fn bitcount_to_u32(bits: gmp::bitcnt_t) -> Option<u32> {
    if bits == !0 {
        None
    } else {
        Some(cast(bits))
    }
}

fn significant_bits_usize(n: &Integer) -> usize {
    // sizeinbase returns 1 if number is 0, so check 0 first
    if n.cmp0() == Ordering::Equal {
        0
    } else {
        unsafe { gmp::mpz_sizeinbase(n.inner(), 2) }
    }
}

impl Inner for Integer {
    type Output = mpz_t;
    #[inline]
    fn inner(&self) -> &mpz_t {
        &self.inner
    }
}

impl InnerMut for Integer {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut mpz_t {
        &mut self.inner
    }
}
