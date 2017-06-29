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

use Assign;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use inner::{Inner, InnerMut};
use ops::{AddFrom, BitAndFrom, BitOrFrom, BitXorFrom, DivFrom, MulFrom,
          NegAssign, NotAssign, Pow, PowAssign, RemFrom, SubFrom};
#[cfg(feature = "rand")]
use rand::RandState;
use std::{i32, u32};
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
               BitXor, BitXorAssign, Deref, Div, DivAssign, Mul, MulAssign,
               Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
               SubAssign};
use std::os::raw::{c_char, c_int, c_long, c_ulong};
use std::slice;
use std::str::FromStr;

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
/// The `Integer` type supports various functions. Most functions have
/// three versions: one that consumes the operand, one that mutates
/// the operand, and one that borrows the operand.
///
/// ```rust
/// use rug::Integer;
/// // 1. consume the operand
/// let a = Integer::from(-15);
/// let abs_a = a.abs();
/// assert_eq!(abs_a, 15);
/// // 2. mutate the operand
/// let mut b = Integer::from(-16);
/// b.abs_mut();
/// assert_eq!(b, 16);
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

impl Default for Integer {
    #[inline]
    fn default() -> Integer {
        Integer::new()
    }
}

impl Clone for Integer {
    #[inline]
    fn clone(&self) -> Integer {
        let mut ret = Integer::new();
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Integer) {
        self.assign(source);
    }
}

impl Drop for Integer {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::mpz_clear(self.inner_mut());
        }
    }
}

impl Hash for Integer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let size = self.inner().size;
        size.hash(state);
        if size != 0 {
            let limbs = size.checked_abs().expect("overflow") as usize;
            let slice = unsafe { slice::from_raw_parts(self.inner().d, limbs) };
            slice.hash(state);
        }
    }
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
        assert_eq!(bits as gmp::bitcnt_t as usize, bits, "overflow");
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init2(ret.inner_mut(), bits as gmp::bitcnt_t);
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
        let limbs = self.inner().alloc;
        let bits = limbs as usize * gmp::LIMB_BITS as usize;
        assert_eq!(
            limbs,
            (bits / gmp::LIMB_BITS as usize) as c_int,
            "overflow"
        );
        bits
    }

    /// Reserves capacity for at least `additional` more bits in the
    /// `Integer`. If the integer already has enough excess capacity,
    /// this function does nothing.
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
        let used_bits = if self.inner().size == 0 {
            0
        } else {
            unsafe { gmp::mpz_sizeinbase(self.inner(), 2) }
        };
        let req_bits = used_bits.checked_add(additional).expect("overflow");
        assert_eq!(req_bits as gmp::bitcnt_t as usize, req_bits, "overflow");
        unsafe {
            gmp::mpz_realloc2(self.inner_mut(), req_bits as gmp::bitcnt_t);
        }
    }

    /// Reserves capacity for at least `additional` more bits in the
    /// `Integer`. If the integer already has enough excess capacity,
    /// this function does nothing.
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
        let used_bits = unsafe { gmp::mpz_sizeinbase(self.inner(), 2) };
        assert_eq!(used_bits as gmp::bitcnt_t as usize, used_bits, "overflow");
        unsafe {
            gmp::mpz_realloc2(self.inner_mut(), used_bits as gmp::bitcnt_t);
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
        Integer::from_f64(val as f64)
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
        use self::ParseIntegerError as Error;
        use self::ParseErrorKind as Kind;

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
                _ => return Err(Error { kind: Kind::InvalidDigit }),
            };
            if digit_value >= radix as u8 {
                return Err(Error { kind: Kind::InvalidDigit });
            }
            got_digit = true;
        }
        if !got_digit {
            return Err(Error { kind: Kind::NoDigits });
        }
        let v = ValidInteger {
            bytes: skip_plus,
            radix: radix,
        };
        Ok(v)
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
    /// let large = Integer::from(123456789012345_u64);
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

    /// Converts to a `u32` if the value fits.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(1234567890);
    /// assert_eq!(fits.to_u32(), Some(1234567890));
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u32(), None);
    /// let large = "123456789012345".parse::<Integer>().unwrap();
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

    /// Converts to an `i32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(-0xabcdef_i32);
    /// assert_eq!(fits.to_i32_wrapping(), -0xabcdef);
    /// let small = Integer::from(0x1_ffff_ffff_u64);
    /// assert_eq!(small.to_i32_wrapping(), -1);
    /// let large = Integer::from_str_radix("1234567890abcdef", 16).unwrap();
    /// assert_eq!(large.to_i32_wrapping(), 0x90abcdef_u32 as i32);
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
    /// let fits = Integer::from(-0xabcdef);
    /// assert_eq!(fits.to_i64_wrapping(), -0xabcdef);
    /// let small = Integer::from_str_radix("1ffffffffffffffff", 16).unwrap();
    /// assert_eq!(small.to_i64_wrapping(), -1);
    /// let large = Integer::from_str_radix("f1234567890abcdef", 16).unwrap();
    /// assert_eq!(large.to_i64_wrapping(), 0x1234567890abcdef_i64);
    /// ```
    #[inline]
    pub fn to_i64_wrapping(&self) -> i64 {
        self.to_u64_wrapping() as i64
    }

    /// Converts to a `u32`, wrapping if the value does not fit.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Integer;
    /// let fits = Integer::from(0x90abcdef_u32);
    /// assert_eq!(fits.to_u32_wrapping(), 0x90abcdef);
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u32_wrapping(), 0xffffffff);
    /// let large = Integer::from_str_radix("1234567890abcdef", 16).unwrap();
    /// assert_eq!(large.to_u32_wrapping(), 0x90abcdef);
    /// ```
    #[inline]
    pub fn to_u32_wrapping(&self) -> u32 {
        let u = unsafe { xgmp::mpz_get_abs_u32(self.inner()) };
        if self.sign() == Ordering::Less {
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
    /// let fits = Integer::from(0x90abcdef_u64);
    /// assert_eq!(fits.to_u64_wrapping(), 0x90abcdef);
    /// let neg = Integer::from(-1);
    /// assert_eq!(neg.to_u64_wrapping(), 0xffff_ffff_ffff_ffff);
    /// let large = Integer::from_str_radix("f123456789abcdef0", 16).unwrap();
    /// assert_eq!(large.to_u64_wrapping(), 0x123456789abcdef0);
    /// ```
    #[inline]
    pub fn to_u64_wrapping(&self) -> u64 {
        let u = unsafe { xgmp::mpz_get_abs_u64(self.inner()) };
        if self.sign() == Ordering::Less {
            u.wrapping_neg()
        } else {
            u
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
    /// let minus_one = min - 1u32;
    /// // minus_one is truncated to f32::MIN
    /// assert_eq!(minus_one.to_f32(), f32::MIN);
    /// let times_two = minus_one * 2u32;
    /// // times_two is too small
    /// assert_eq!(times_two.to_f32(), f32::NEG_INFINITY);
    /// ```
    #[inline]
    pub fn to_f32(&self) -> f32 {
        trunc_f64_to_f32(self.to_f64())
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
    /// assert_eq!(j.to_f64(), trunc as f64);
    ///
    /// let max = Integer::from_f64(f64::MAX).unwrap();
    /// let plus_one = max + 1u32;
    /// // plus_one is truncated to f64::MAX
    /// assert_eq!(plus_one.to_f64(), f64::MAX);
    /// let times_two = plus_one * 2u32;
    /// // times_two is too large
    /// assert_eq!(times_two.to_f64(), f64::INFINITY);
    /// ```
    #[inline]
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpz_get_d(self.inner()) }
    }

    /// Converts to an `f32` and an exponent, rounding towards zero.
    ///
    /// The returned `f32` is in the range 0.5 ≤ *x* < 1.
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
        let trunc_f = trunc_f64_to_f32(f);
        (trunc_f, exp)
    }

    /// Converts to an `f64` and an exponent, rounding towards zero.
    ///
    /// The returned `f64` is in the range 0.5 ≤ *x* < 1.
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
        assert_eq!(exp as u32 as c_long, exp, "overflow");
        (f, exp as u32)
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
    /// i.assign_str_radix("1234567890aAbBcCdDeEfF", 16).unwrap();
    /// assert_eq!(i.to_string_radix(16), "1234567890aabbccddeeff");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix(&self, radix: i32) -> String {
        make_string(self, radix, false)
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
        self.assign_f64(val as f64)
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
    /// The returned object implements `Deref` with an `Integer`
    /// target. This method performs a shallow copy and negates it, and
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
    /// The returned object implements `Deref` with an `Integer`
    /// target. This method performs a shallow copy and possibly
    /// negates it, and negation does not change the allocated data.
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
    /// assert_eq!(Integer::from(-5).sign(), Ordering::Less);
    /// assert_eq!(Integer::from(0).sign(), Ordering::Equal);
    /// assert_eq!(Integer::from(5).sign(), Ordering::Greater);
    /// ```
    #[inline]
    pub fn sign(&self) -> Ordering {
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
    /// assert_eq!(Integer::from(-2).find_zero(0), Some(0));
    /// assert_eq!(Integer::from(-2).find_zero(1), None);
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
    /// assert_eq!(Integer::from(1).find_one(0), Some(0));
    /// assert_eq!(Integer::from(1).find_one(1), None);
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
        bitcount_to_u32(
            unsafe { gmp::mpz_hamdist(self.inner(), other.inner()) },
        )
    }

    math_op1! {
        Integer;
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
        Integer;
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
        Integer;
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
        Integer;
        xgmp::mpz_tdiv_qr_check_0;
        /// Performs a division producing both the quotient and
        /// remainder.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(10);
        /// let (quotient, rem) = dividend.div_rem(divisor);
        /// assert_eq!(quotient, 2);
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
        /// The quotient is stored in `self` and the remainder is
        /// stored in `divisor`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let mut dividend_quotient = Integer::from(23);
        /// let mut divisor_rem = Integer::from(10);
        /// dividend_quotient.div_rem_mut(&mut divisor_rem);
        /// assert_eq!(dividend_quotient, 2);
        /// assert_eq!(divisor_rem, 3);
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if `divisor` is zero.
        fn div_rem_mut;
        /// Performs a division producing both the quotient and
        /// remainder.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Integer;
        /// let dividend = Integer::from(23);
        /// let divisor = Integer::from(10);
        /// let r = dividend.div_rem_ref(&divisor);
        /// let (quotient, rem) = <(Integer, Integer)>::from(r);
        /// assert_eq!(quotient, 2);
        /// assert_eq!(rem, 3);
        /// ```
        fn div_rem_ref -> DivRemRef;
    }
    math_op2! {
        Integer;
        xgmp::mpz_divexact_check_0;
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
        Integer;
        xgmp::mpz_divexact_ui_check_0;
        /// Performs an exact division. This is much faster than
        /// normal division, but produces correct results only when
        /// the division is exact.
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
        /// Performs an exact division. This is much faster than
        /// normal division, but produces correct results only when
        /// the division is exact.
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
        /// Performs an exact division. This is much faster than
        /// normal division, but produces correct results only when
        /// the division is exact.
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
            xgmp::mpz_invert_check_0(
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
    /// match ans {
    ///     Ok(_) => unreachable!(),
    ///     Err(ref unchanged) => assert_eq!(*unchanged, 0),
    /// }
    /// // Modulo 5, the inverse of 2 is 3, as 2 * 3 = 1.
    /// ans.assign(n.invert_ref(&Integer::from(5)));
    /// match ans {
    ///     Ok(ref inverse) => assert_eq!(*inverse, 3),
    ///     Err(_) => unreachable!(),
    /// };
    /// ```
    #[inline]
    pub fn invert_ref<'a>(&'a self, modulo: &'a Integer) -> InvertRef<'a> {
        InvertRef {
            ref_self: self,
            modulo: modulo,
        }
    }

    /// Raises a number to the power of `power` modulo `modulo` and
    /// returns `Ok(raised)` if an answer exists, or `Err(unchanged)`
    /// if it does not.
    ///
    /// If `power` is negative, then the number must have an inverse
    /// modulo `modulo` for an answer to exist.
    ///
    /// # Examples
    ///
    /// When the power is positive, an answer always exists.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 7 ^ 5 = 16807
    /// let n = Integer::from(7);
    /// let pow = Integer::from(5);
    /// let m = Integer::from(1000);
    /// let raised = match n.pow_mod(&pow, &m) {
    ///     Ok(raised) => raised,
    ///     Err(_) => unreachable!(),
    /// };
    /// assert_eq!(raised, 807);
    /// ```
    ///
    /// When the power is negative, an answer exists if an inverse
    /// exists.
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// let n = Integer::from(7);
    /// let pow = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let raised = match n.pow_mod(&pow, &m) {
    ///     Ok(raised) => raised,
    ///     Err(_) => unreachable!(),
    /// };
    /// assert_eq!(raised, 943);
    /// ```
    #[inline]
    pub fn pow_mod(
        mut self,
        power: &Integer,
        modulo: &Integer,
    ) -> Result<Integer, Integer> {
        if self.pow_mod_mut(power, modulo) {
            Ok(self)
        } else {
            Err(self)
        }
    }

    /// Raises a number to the power of `power` modulo `modulo` and
    /// returns `true` if an answer exists.
    ///
    /// If `power` is negative, then the number must have an inverse
    /// modulo `modulo` for an answer to exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// // Modulo 1000, 2 has no inverse: there is no x such that 2 * x =  1.
    /// let mut n = Integer::from(2);
    /// let pow = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let exists = n.pow_mod_mut(&pow, &m);
    /// assert!(!exists);
    /// assert_eq!(n, 2);
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// n.assign(7);
    /// let exists = n.pow_mod_mut(&pow, &m);
    /// assert!(exists);
    /// assert_eq!(n, 943);
    /// ```
    pub fn pow_mod_mut(&mut self, power: &Integer, modulo: &Integer) -> bool {
        let abs_pow;
        let pow_inner = if power.sign() == Ordering::Less {
            if !(self.invert_mut(modulo)) {
                return false;
            }
            abs_pow = power.as_neg();
            abs_pow.inner()
        } else {
            power.inner()
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

    /// Raises a number to the power of `power` modulo `modulo` if an
    /// answer exists.
    ///
    /// If `power` is negative, then the number must have an inverse
    /// modulo `modulo` for an answer to exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// // Modulo 1000, 2 has no inverse: there is no x such that 2 * x =  1.
    /// let two = Integer::from(2);
    /// let pow = Integer::from(-5);
    /// let m = Integer::from(1000);
    /// let mut ans = Result::from(two.pow_mod_ref(&pow, &m));
    /// match ans {
    ///     Ok(_) => unreachable!(),
    ///     Err(ref unchanged) => assert_eq!(*unchanged, 0),
    /// }
    /// // 7 * 143 modulo 1000 = 1, so 7 has an inverse 143.
    /// // 7 ^ -5 modulo 1000 = 143 ^ 5 modulo 1000 = 943.
    /// let seven = Integer::from(7);
    /// ans.assign(seven.pow_mod_ref(&pow, &m));
    /// match ans {
    ///     Ok(ref raised) => assert_eq!(*raised, 943),
    ///     Err(_) => unreachable!(),
    /// }
    /// ```
    #[inline]
    pub fn pow_mod_ref<'a>(
        &'a self,
        power: &'a Integer,
        modulo: &'a Integer,
    ) -> PowModRef<'a> {
        PowModRef {
            ref_self: self,
            power: power,
            modulo: modulo,
        }
    }

    /// Raises `base` to the power of `power`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 12);
    /// assert_eq!(i, 13_u64.pow(12));
    /// ```
    #[inline]
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
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_i_pow_u(-13, 12);
    /// assert_eq!(i, (-13_i64).pow(12));
    /// i.assign_i_pow_u(-13, 13);
    /// assert_eq!(i, (-13_i64).pow(13));
    /// ```
    #[inline]
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
        Integer;
        gmp::mpz_root;
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
        fn root_mut;
        /// Computes the <i>n</i>th root and truncates the result.
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
        Integer;
        gmp::mpz_rootrem;
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
        fn root_rem_mut;
        /// Computes the <i>n</i>th root and returns the truncated
        /// root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root raised to the power of *n*.
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
        fn root_rem_ref -> RootRemRef;
    }
    math_op1! {
        Integer;
        gmp::mpz_sqrt;
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
        fn sqrt_mut;
        /// Computes the square root and truncates the result.
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
        Integer;
        gmp::mpz_sqrtrem;
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
        fn sqrt_rem_mut;
        /// Computes the square root and the remainder.
        ///
        /// The remainder is the original number minus the truncated
        /// root squared.
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
        let p = unsafe { gmp::mpz_probab_prime_p(self.inner(), reps as c_int) };
        match p {
            0 => IsPrime::No,
            1 => IsPrime::Probably,
            2 => IsPrime::Yes,
            _ => unreachable!(),
        }
    }

    math_op1! {
        Integer;
        gmp::mpz_nextprime;
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        fn next_prime();
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        fn next_prime_mut;
        /// Identifies primes using a probabilistic algorithm; the
        /// chance of a composite passing will be extremely small.
        fn next_prime_ref -> NextPrimeRef;
    }
    math_op2! {
        Integer;
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
    math_op2! {
        Integer;
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
    #[inline]
    pub fn jacobi(&self, n: &Integer) -> i32 {
        unsafe { gmp::mpz_jacobi(self.inner(), n.inner()) as i32 }
    }

    /// Calculates the Legendre symbol (`self`/<i>p</i>).
    #[inline]
    pub fn legendre(&self, p: &Integer) -> i32 {
        unsafe { gmp::mpz_legendre(self.inner(), p.inner()) as i32 }
    }

    /// Calculates the Jacobi symbol (`self`/<i>n</i>) with the
    /// Kronecker extension.
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
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 50);
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
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 50);
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
        assert_eq!(cnt as u32 as gmp::bitcnt_t, cnt, "overflow");
        cnt as u32
    }

    /// Removes all occurrences of `factor`, and counts the number of
    /// occurrences removed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::new();
    /// i.assign_u_pow_u(13, 50);
    /// i *= 1000;
    /// let (mut j, mut count) = (Integer::new(), 0);
    /// (&mut j, &mut count).assign(i.remove_factor_ref(&Integer::from(13)));
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
            factor: factor,
        }
    }

    /// Computes the factorial of *n*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
    /// i.assign_factorial(10);
    /// assert_eq!(i, 3628800);
    /// ```
    #[inline]
    pub fn assign_factorial(&mut self, n: u32) {
        unsafe {
            gmp::mpz_fac_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes the double factorial of *n*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 8 * 6 * 4 * 2
    /// i.assign_factorial_2(10);
    /// assert_eq!(i, 3840);
    /// ```
    #[inline]
    pub fn assign_factorial_2(&mut self, n: u32) {
        unsafe {
            gmp::mpz_2fac_ui(self.inner_mut(), n.into());
        }
    }

    /// Computes the *m*-multi factorial of *n*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// // 10 * 7 * 4 * 1
    /// i.assign_factorial_m(10, 3);
    /// assert_eq!(i, 280);
    /// ```
    #[inline]
    pub fn assign_factorial_m(&mut self, n: u32, m: u32) {
        unsafe {
            gmp::mpz_mfac_uiui(self.inner_mut(), n.into(), m.into());
        }
    }

    /// Computes the primorial of *n*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// // 7 * 5 * 3 * 2
    /// i.assign_primorial(10);
    /// assert_eq!(i, 210);
    /// ```
    #[inline]
    pub fn assign_primorial(&mut self, n: u32) {
        unsafe {
            gmp::mpz_primorial_ui(self.inner_mut(), n.into());
        }
    }

    math_op1! {
        Integer;
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

    /// Computes the binomial coefficient *n* over *k*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// // 7 choose 2 is 21
    /// let mut i = Integer::new();
    /// i.assign_binomial_u(7, 2);
    /// assert_eq!(i, 21);
    /// ```
    #[inline]
    pub fn assign_binomial_u(&mut self, n: u32, k: u32) {
        unsafe {
            gmp::mpz_bin_uiui(self.inner_mut(), n.into(), k.into());
        }
    }

    /// Computes the Fibonacci number.
    ///
    /// This function is meant for an isolated number. If a sequence
    /// of Fibonacci numbers is required, the first two values of the
    /// sequence should be computed with the
    /// [`assign_fibonacci_2`](#method.assign_fibonacci_2) method,
    /// then iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_fibonacci(12);
    /// assert_eq!(i, 144);
    /// ```
    #[inline]
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
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// let mut j = Integer::new();
    /// i.assign_fibonacci_2(&mut j, 12);
    /// assert_eq!(i, 144);
    /// assert_eq!(j, 89);
    /// // Fibonacci number F[-1] is 1
    /// i.assign_fibonacci_2(&mut j, 0);
    /// assert_eq!(i, 0);
    /// assert_eq!(j, 1);
    /// ```
    #[inline]
    pub fn assign_fibonacci_2(&mut self, previous: &mut Integer, n: u32) {
        unsafe {
            gmp::mpz_fib2_ui(self.inner_mut(), previous.inner_mut(), n.into());
        }
    }

    /// Computes the Lucas number.
    ///
    /// This function is meant for an isolated number. If a sequence
    /// of Lucas numbers is required, the first two values of the
    /// sequence should be computed with the
    /// [`assign_lucas_2`](#method.assign_lucas_2) method, then
    /// iterations should be used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// i.assign_lucas(12);
    /// assert_eq!(i, 322);
    /// ```
    #[inline]
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
    /// use rug::Integer;
    /// let mut i = Integer::new();
    /// let mut j = Integer::new();
    /// i.assign_lucas_2(&mut j, 12);
    /// assert_eq!(i, 322);
    /// assert_eq!(j, 199);
    /// i.assign_lucas_2(&mut j, 0);
    /// assert_eq!(i, 2);
    /// assert_eq!(j, -1);
    /// ```
    #[inline]
    pub fn assign_lucas_2(&mut self, previous: &mut Integer, n: u32) {
        unsafe {
            gmp::mpz_lucnum2_ui(
                self.inner_mut(),
                previous.inner_mut(),
                n.into(),
            );
        }
    }

    #[cfg(feature = "rand")]
    /// Generates a random number with a specified maximum number of
    /// bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::rand::RandState;
    /// let mut rand = RandState::new();
    /// let mut i = Integer::new();
    /// i.assign_random_bits(0, &mut rand);
    /// assert_eq!(i, 0);
    /// i.assign_random_bits(80, &mut rand);
    /// assert!(i.significant_bits() <= 80);
    /// ```
    #[inline]
    pub fn assign_random_bits(&mut self, bits: u32, rng: &mut RandState) {
        unsafe {
            gmp::mpz_urandomb(self.inner_mut(), rng.inner_mut(), bits.into());
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
    /// let i = Integer::from(15);
    /// let below = i.random_below(&mut rand);
    /// println!("0 <= {} < 15", below);
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
    /// println!("0 <= {} < 15", i);
    /// assert!(i < 15);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[inline]
    pub fn random_below_mut(&mut self, rng: &mut RandState) {
        assert_eq!(self.sign(), Ordering::Greater, "cannot be below zero");
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
    /// let mut i = Integer::new();
    /// i.assign_random_below(&bound, &mut rand);
    /// println!("0 <= {} < {}", i, bound);
    /// assert!(i < bound);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    #[inline]
    pub fn assign_random_below(
        &mut self,
        bound: &Integer,
        rng: &mut RandState,
    ) {
        assert_eq!(bound.sign(), Ordering::Greater, "cannot be below zero");
        unsafe {
            gmp::mpz_urandomm(self.inner_mut(), rng.inner_mut(), bound.inner());
        }
    }
}

impl<'a> From<&'a Integer> for Integer {
    #[inline]
    fn from(val: &Integer) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set(ret.inner_mut(), val.inner());
            ret
        }
    }
}

impl From<i32> for Integer {
    #[inline]
    fn from(val: i32) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_si(ret.inner_mut(), val.into());
            ret
        }
    }
}

impl From<i64> for Integer {
    #[inline]
    fn from(val: i64) -> Integer {
        if mem::size_of::<c_long>() >= 8 {
            unsafe {
                let mut ret: Integer = mem::uninitialized();
                gmp::mpz_init_set_si(ret.inner_mut(), val as c_long);
                ret
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

impl From<u32> for Integer {
    #[inline]
    fn from(val: u32) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_ui(ret.inner_mut(), val.into());
            ret
        }
    }
}

impl From<u64> for Integer {
    #[inline]
    fn from(val: u64) -> Integer {
        if mem::size_of::<c_ulong>() >= 8 {
            unsafe {
                let mut ret: Integer = mem::uninitialized();
                gmp::mpz_init_set_ui(ret.inner_mut(), val as c_ulong);
                ret
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

impl FromStr for Integer {
    type Err = ParseIntegerError;
    #[inline]
    fn from_str(src: &str) -> Result<Integer, ParseIntegerError> {
        let mut i = Integer::new();
        i.assign_str(src)?;
        Ok(i)
    }
}

impl Display for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl Assign for Integer {
    #[inline]
    fn assign(&mut self, mut other: Integer) {
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Integer> for Integer {
    #[inline]
    fn assign(&mut self, other: &'a Integer) {
        unsafe {
            gmp::mpz_set(self.inner_mut(), other.inner());
        }
    }
}

impl Assign<i32> for Integer {
    #[inline]
    fn assign(&mut self, val: i32) {
        unsafe {
            xgmp::mpz_set_i32(self.inner_mut(), val);
        }
    }
}

impl Assign<i64> for Integer {
    #[inline]
    fn assign(&mut self, val: i64) {
        unsafe {
            xgmp::mpz_set_i64(self.inner_mut(), val);
        }
    }
}

impl Assign<u32> for Integer {
    #[inline]
    fn assign(&mut self, val: u32) {
        unsafe {
            xgmp::mpz_set_u32(self.inner_mut(), val);
        }
    }
}

impl Assign<u64> for Integer {
    #[inline]
    fn assign(&mut self, val: u64) {
        unsafe {
            xgmp::mpz_set_u64(self.inner_mut(), val);
        }
    }
}

ref_math_op1! { Integer; gmp::mpz_abs; struct AbsRef {} }
ref_math_op1! { Integer; gmp::mpz_fdiv_r_2exp; struct KeepBitsRef { n: u32 } }
ref_math_op1! { Integer; xgmp::mpz_next_pow_of_two; struct NextPowerTwoRef {} }
ref_math_op2_2! {
    Integer; xgmp::mpz_tdiv_qr_check_0; struct DivRemRef { divisor }
}
ref_math_op2! {
    Integer; xgmp::mpz_divexact_check_0; struct DivExactRef { divisor }
}
ref_math_op1! {
    Integer; xgmp::mpz_divexact_ui_check_0; struct DivExactURef { divisor: u32 }
}

#[derive(Clone, Copy)]
pub struct PowModRef<'a> {
    ref_self: &'a Integer,
    power: &'a Integer,
    modulo: &'a Integer,
}

impl<'a> From<PowModRef<'a>> for Result<Integer, Integer> {
    fn from(src: PowModRef<'a>) -> Result<Integer, Integer> {
        if src.power.sign() == Ordering::Less {
            let mut ret = Result::from(src.ref_self.invert_ref(src.modulo));
            match ret {
                Ok(ref mut inv) => {
                    let abs_pow = src.power.as_neg();
                    unsafe {
                        gmp::mpz_powm(
                            inv.inner_mut(),
                            inv.inner(),
                            abs_pow.inner(),
                            src.modulo.inner(),
                        );
                    }
                }
                Err(_) => {}
            };
            ret
        } else {
            let mut ret = Ok(Integer::new());
            match ret {
                Ok(ref mut dest) => unsafe {
                    gmp::mpz_powm(
                        dest.inner_mut(),
                        src.ref_self.inner(),
                        src.power.inner(),
                        src.modulo.inner(),
                    );
                },
                Err(_) => unreachable!(),
            };
            ret
        }
    }
}

impl<'a> Assign<PowModRef<'a>> for Result<Integer, Integer> {
    fn assign(&mut self, src: PowModRef<'a>) {
        if src.power.sign() == Ordering::Less {
            self.assign(src.ref_self.invert_ref(src.modulo));
            match *self {
                Ok(ref mut inv) => {
                    let abs_pow = src.power.as_neg();
                    unsafe {
                        gmp::mpz_powm(
                            inv.inner_mut(),
                            inv.inner(),
                            abs_pow.inner(),
                            src.modulo.inner(),
                        );
                    }
                }
                Err(_) => {}
            }
        } else {
            if self.is_err() {
                result_swap(self);
            }
            match *self {
                Ok(ref mut dest) => unsafe {
                    gmp::mpz_powm(
                        dest.inner_mut(),
                        src.ref_self.inner(),
                        src.power.inner(),
                        src.modulo.inner(),
                    );
                },
                Err(_) => unreachable!(),
            }
        }
    }
}

ref_math_op1! { Integer; gmp::mpz_root; struct RootRef { n: u32 } }
ref_math_op1_2! { Integer; gmp::mpz_rootrem; struct RootRemRef { n: u32 } }
ref_math_op1! { Integer; gmp::mpz_sqrt; struct SqrtRef {} }
ref_math_op1_2! { Integer; gmp::mpz_sqrtrem; struct SqrtRemRef {} }
ref_math_op1! { Integer; gmp::mpz_nextprime; struct NextPrimeRef {} }
ref_math_op2! { Integer; gmp::mpz_gcd; struct GcdRef { other } }
ref_math_op2! { Integer; gmp::mpz_lcm; struct LcmRef { other } }

#[derive(Clone, Copy)]
pub struct InvertRef<'a> {
    ref_self: &'a Integer,
    modulo: &'a Integer,
}

impl<'a> From<InvertRef<'a>> for Result<Integer, Integer> {
    #[inline]
    fn from(src: InvertRef<'a>) -> Result<Integer, Integer> {
        let mut i = Integer::new();
        let exists = unsafe {
            xgmp::mpz_invert_check_0(
                i.inner_mut(),
                src.ref_self.inner(),
                src.modulo.inner(),
            ) != 0
        };
        if exists {
            Ok(i)
        } else {
            Err(i)
        }
    }
}

impl<'a> Assign<InvertRef<'a>> for Result<Integer, Integer> {
    #[inline]
    fn assign(&mut self, src: InvertRef<'a>) {
        let exists = {
            let dest = match *self {
                Ok(ref mut i) | Err(ref mut i) => i,
            };
            unsafe {
                xgmp::mpz_invert_check_0(
                    dest.inner_mut(),
                    src.ref_self.inner(),
                    src.modulo.inner(),
                ) != 0
            }
        };
        if exists != self.is_ok() {
            result_swap(self);
        }
    }
}

#[derive(Clone, Copy)]
pub struct RemoveFactorRef<'a> {
    ref_self: &'a Integer,
    factor: &'a Integer,
}

impl<'a> Assign<RemoveFactorRef<'a>> for (&'a mut Integer, &'a mut u32) {
    #[inline]
    fn assign(&mut self, src: RemoveFactorRef<'a>) {
        let cnt = unsafe {
            gmp::mpz_remove(
                self.0.inner_mut(),
                src.ref_self.inner(),
                src.factor.inner(),
            )
        };
        assert_eq!(cnt as u32 as gmp::bitcnt_t, cnt, "overflow");
        *self.1 = cnt as u32;
    }
}

ref_math_op1! { Integer; gmp::mpz_bin_ui; struct BinomialRef { k: u32 } }

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

arith_unary! { Integer; gmp::mpz_neg; Neg neg; NegAssign neg_assign; NegRef }
arith_binary! {
    Integer;
    gmp::mpz_add;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    AddRef
}
arith_binary! {
    Integer;
    gmp::mpz_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    SubRef
}
arith_binary! {
    Integer;
    gmp::mpz_mul;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    MulRef
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_q_check_0;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    DivRef
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_r_check_0;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    RemRef
}
arith_unary! { Integer; gmp::mpz_com; Not not; NotAssign not_assign; NotRef }
arith_binary! {
    Integer;
    gmp::mpz_and;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    BitAndRef
}
arith_binary! {
    Integer;
    gmp::mpz_ior;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    BitOrRef
}
arith_binary! {
    Integer;
    gmp::mpz_xor;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    BitXorRef
}

arith_prim_commut! {
    Integer;
    xgmp::mpz_add_si;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    i32;
    AddRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_sub_si, xgmp::mpz_si_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    i32;
    SubRefI32 SubFromRefI32
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_si;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    i32;
    MulRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_si_check_0, xgmp::mpz_si_tdiv_q_check_0;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    i32;
    DivRefI32 DivFromRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_si_check_0, xgmp::mpz_si_tdiv_r_check_0;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    i32;
    RemRefI32 RemFromRefI32
}
arith_prim! {
    Integer; xgmp::mpz_lshift_si; Shl shl; ShlAssign shl_assign; i32; ShlRefI32
}
arith_prim! {
    Integer; xgmp::mpz_rshift_si; Shr shr; ShrAssign shr_assign; i32; ShrRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_si;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    i32;
    BitAndRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_si;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    i32;
    BitOrRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_si;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    i32;
    BitXorRefI32
}

arith_prim_commut! {
    Integer;
    gmp::mpz_add_ui;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    u32;
    AddRefU32
}
arith_prim_noncommut! {
    Integer;
    gmp::mpz_sub_ui, gmp::mpz_ui_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    u32;
    SubRefU32 SubFromRefU32
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_ui;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    u32;
    MulRefU32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_ui_check_0, xgmp::mpz_ui_tdiv_q_check_0;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    u32;
    DivRefU32 DivFromRefU32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_ui_check_0, xgmp::mpz_ui_tdiv_r_check_0;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    u32;
    RemRefU32 RemFromRefU32
}
arith_prim! {
    Integer; gmp::mpz_mul_2exp; Shl shl; ShlAssign shl_assign; u32; ShlRefU32
}
arith_prim! {
    Integer; gmp::mpz_fdiv_q_2exp; Shr shr; ShrAssign shr_assign; u32; ShrRefU32
}
arith_prim! {
    Integer; gmp::mpz_pow_ui; Pow pow; PowAssign pow_assign; u32; PowRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_ui;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    u32;
    BitAndRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_ui;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    u32;
    BitOrRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_ui;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    u32;
    BitXorRefU32
}

macro_rules! op_mul {
    {
        $(#[$attr:meta])* impl $Imp:ident $method:ident;
        $(#[$attr_assign:meta])* impl $ImpAssign:ident $method_assign:ident;
        $Ref:ident, $rhs_method:ident, $func:path
    } => {
        impl<'a> $Imp<$Ref<'a>> for Integer {
            type Output = Integer;
            $(#[$attr])*
                #[inline]
            fn $method(mut self, rhs: $Ref) -> Integer {
                self.$method_assign(rhs);
                self
            }
        }

        impl<'a> $ImpAssign<$Ref<'a>> for Integer  {
            $(#[$attr_assign])*
                #[inline]
            fn $method_assign(&mut self, rhs: $Ref) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        rhs.lhs.inner(),
                        rhs.rhs.$rhs_method()
                    );
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
    /// use rug::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let init = Integer::from(100);
    /// let acc = init + &m1 * &m2;
    /// assert_eq!(acc, 121);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let mut acc = Integer::from(100);
    /// acc += &m1 * &m2;
    /// assert_eq!(acc, 121);
    /// ```
    impl AddAssign add_assign;
    MulRef, inner, gmp::mpz_addmul
}

op_mul! {
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init + &m * 7u32;
    /// assert_eq!(acc, 121);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc += &m * 7u32;
    /// assert_eq!(acc, 121);
    /// ```
    impl AddAssign add_assign;
    MulRefU32, into, gmp::mpz_addmul_ui
}

op_mul! {
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init + &m * -7i32;
    /// assert_eq!(acc, 79);
    /// ```
    impl Add add;
    /// Peforms multiplication and addition together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc += &m * -7i32;
    /// assert_eq!(acc, 79);
    /// ```
    impl AddAssign add_assign;
    MulRefI32, into, xgmp::mpz_addmul_si
}

op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let init = Integer::from(100);
    /// let acc = init - &m1 * &m2;
    /// assert_eq!(acc, 79);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m1 = Integer::from(3);
    /// let m2 = Integer::from(7);
    /// let mut acc = Integer::from(100);
    /// acc -= &m1 * &m2;
    /// assert_eq!(acc, 79);
    /// ```
    impl SubAssign sub_assign;
    MulRef, inner, gmp::mpz_submul
}

op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init - &m * 7u32;
    /// assert_eq!(acc, 79);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc -= &m * 7u32;
    /// assert_eq!(acc, 79);
    /// ```
    impl SubAssign sub_assign;
    MulRefU32, into, gmp::mpz_submul_ui
}

op_mul! {
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let init = Integer::from(100);
    /// let acc = init - &m * -7i32;
    /// assert_eq!(acc, 121);
    /// ```
    impl Sub sub;
    /// Peforms multiplication and subtraction together.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// let m = Integer::from(3);
    /// let mut acc = Integer::from(100);
    /// acc -= &m * -7i32;
    /// assert_eq!(acc, 121);
    /// ```
    impl SubAssign sub_assign;
    MulRefI32, into, xgmp::mpz_submul_si
}

impl Eq for Integer {}

impl Ord for Integer {
    #[inline]
    fn cmp(&self, other: &Integer) -> Ordering {
        let ord = unsafe { gmp::mpz_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Integer {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd for Integer {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $T:ty, $func:path } => {
        impl PartialEq<$T> for Integer {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialEq<Integer> for $T {
            #[inline]
            fn eq(&self, other: &Integer) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<$T> for Integer {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                let ord = unsafe { $func(self.inner(), (*other).into()) };
                Some(ord.cmp(&0))
            }
        }

        impl PartialOrd<Integer> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    };
}

cmp! { i32, xgmp::mpz_cmp_i32 }
cmp! { i64, xgmp::mpz_cmp_i64 }
cmp! { u32, xgmp::mpz_cmp_u32 }
cmp! { u64, xgmp::mpz_cmp_u64 }

impl PartialEq<f32> for Integer {
    #[inline]
    fn eq(&self, other: &f32) -> bool {
        let o = *other as f64;
        self.eq(&o)
    }
}

impl PartialEq<Integer> for f32 {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<f32> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &f32) -> Option<Ordering> {
        let o = *other as f64;
        self.partial_cmp(&o)
    }
}

impl PartialOrd<Integer> for f32 {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        other.partial_cmp(self).map(Ordering::reverse)
    }
}

impl PartialEq<f64> for Integer {
    #[inline]
    fn eq(&self, other: &f64) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialEq<Integer> for f64 {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<f64> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if other.is_nan() {
            None
        } else {
            let ord = unsafe { gmp::mpz_cmp_d(self.inner(), *other) };
            Some(ord.cmp(&0))
        }
    }
}

impl PartialOrd<Integer> for f64 {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        other.partial_cmp(self).map(Ordering::reverse)
    }
}

fn make_string(i: &Integer, radix: i32, to_upper: bool) -> String {
    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let i_size = unsafe { gmp::mpz_sizeinbase(i.inner(), radix) };
    // size + 2 for '-' and nul
    let size = i_size.checked_add(2).unwrap();
    let mut buf = Vec::<u8>::with_capacity(size);
    let case_radix = if to_upper { -radix } else { radix };
    unsafe {
        buf.set_len(size);
        gmp::mpz_get_str(
            buf.as_mut_ptr() as *mut c_char,
            case_radix as c_int,
            i.inner(),
        );
        let nul_index = buf.iter().position(|&x| x == 0).unwrap();
        buf.set_len(nul_index);
        String::from_utf8_unchecked(buf)
    }
}

fn fmt_radix(
    i: &Integer,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let s = make_string(i, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

/// A validated string that can always be converted to an
/// [`Integer`](../struct.Integer.html).
///
/// See the [`Integer::valid_str_radix`]
/// (../struct.Integer.html#method.valid_str_radix) method.
#[derive(Clone, Debug)]
pub struct ValidInteger<'a> {
    bytes: &'a [u8],
    radix: i32,
}

from_borrow! { ValidInteger<'a> => Integer }

impl<'a> Assign<ValidInteger<'a>> for Integer {
    #[inline]
    fn assign(&mut self, rhs: ValidInteger) {
        let mut v = Vec::<u8>::with_capacity(rhs.bytes.len() + 1);
        v.extend_from_slice(rhs.bytes);
        v.push(0);
        let err = unsafe {
            let c_str = CStr::from_bytes_with_nul_unchecked(&v);
            gmp::mpz_set_str(self.inner_mut(), c_str.as_ptr(), rhs.radix.into())
        };
        assert_eq!(err, 0);
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing an `Integer`.
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

impl Display for ParseIntegerError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// Whether a number is prime.
pub enum IsPrime {
    /// The number is definitely not prime.
    No,
    /// The number is probably prime.
    Probably,
    /// The number is definitely prime.
    Yes,
}

unsafe impl Send for Integer {}
unsafe impl Sync for Integer {}

fn bitcount_to_u32(bits: gmp::bitcnt_t) -> Option<u32> {
    let max: gmp::bitcnt_t = !0;
    if bits == max {
        None
    } else {
        assert_eq!(bits as u32 as gmp::bitcnt_t, bits, "overflow");
        Some(bits as u32)
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

fn trunc_f64_to_f32(f: f64) -> f32 {
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

// The commented out function results in longer x86_64 asm.
// fn result_swap<T>(r: &mut Result<T, T>) {
//     let old = mem::replace(r, unsafe { mem::uninitialized() });
//     let new = match old {
//         Ok(t) => Err(t),
//         Err(t) => Ok(t),
//     };
//     mem::forget(mem::replace(r, new));
// }
fn result_swap<T>(r: &mut Result<T, T>) {
    if r.is_ok() {
        let val = match *r {
            Ok(ref mut val) => {
                mem::replace(val, unsafe { mem::uninitialized() })
            }
            Err(_) => unreachable!(),
        };
        mem::forget(mem::replace(r, Err(val)));
    } else {
        let val = match *r {
            Err(ref mut val) => {
                mem::replace(val, unsafe { mem::uninitialized() })
            }
            Ok(_) => unreachable!(),
        };
        mem::forget(mem::replace(r, Ok(val)));
    }
}
