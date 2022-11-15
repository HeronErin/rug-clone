// Copyright © 2016–2022 Trevor Spiteri

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License and
// a copy of the GNU General Public License along with this program. If not, see
// <https://www.gnu.org/licenses/>.

use crate::ext::xmpz;
use crate::misc;
use crate::{Assign, Complete, Integer};
use az::UnwrappedCast;
use gmp_mpfr_sys::gmp::bitcnt_t;

pub trait Sealed {}
impl Sealed for Integer {}

/// [`Integer`] extension trait with 64-bit alternatives of some methods.
///
/// Various [`Integer`] methods use 32-bit values for things like bit count or
/// exponents. On some platforms, alternatives of these methods using 64-bit
/// values are supported. This trait is only implemented on platforms where
/// these 64-bit methods are supported.
///
/// This trait is sealed and is only implemented for [`Integer`].
pub trait IntegerExt64: Sealed {
    /// Converts to an [`f32`] and an exponent, rounding towards zero.
    ///
    /// The returned [`f32`] is in the range
    /// 0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1. If the value is zero, `(0.0, 0)`
    /// is returned.
    ///
    /// This method is similar to [`to_f32_exp`][Integer::to_f32_exp] but
    /// returns the exponent as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let zero = Integer::new();
    /// let (d0, exp0) = zero.to_f32_exp64();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let fifteen = Integer::from(15);
    /// let (d15, exp15) = fifteen.to_f32_exp64();
    /// assert_eq!((d15, exp15), (15.0 / 16.0, 4));
    /// ```
    fn to_f32_exp64(&self) -> (f32, u64);

    /// Converts to an [`f64`] and an exponent, rounding towards zero.
    ///
    /// The returned [`f64`] is in the range
    /// 0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1. If the value is zero, `(0.0, 0)`
    /// is returned.
    ///
    /// This method is similar to [`to_f64_exp`][Integer::to_f64_exp] but
    /// returns the exponent as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let zero = Integer::new();
    /// let (d0, exp0) = zero.to_f64_exp64();
    /// assert_eq!((d0, exp0), (0.0, 0));
    /// let fifteen = Integer::from(15);
    /// let (d15, exp15) = fifteen.to_f64_exp64();
    /// assert_eq!((d15, exp15), (15.0 / 16.0, 4));
    /// ```
    fn to_f64_exp64(&self) -> (f64, u64);

    /// Returns [`true`] if the number is divisible by `divisor`. Unlike other
    /// division functions, `divisor` can be zero.
    ///
    /// This method is similar to [`is_divisible_u`][Integer::is_divisible_u]
    /// but takes the divisor as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(230);
    /// assert!(i.is_divisible_u64(23));
    /// assert!(!i.is_divisible_u64(100));
    /// assert!(!i.is_divisible_u64(0));
    /// ```
    fn is_divisible_u64(&self, divisor: u64) -> bool;

    /// Returns [`true`] if the number is divisible by 2<sup><i>b</i></sup>.
    ///
    /// This method is similar to
    /// [`is_divisible_2pow`][Integer::is_divisible_2pow] but takes `b` as
    /// [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(15 << 17);
    /// assert!(i.is_divisible_2pow_64(16));
    /// assert!(i.is_divisible_2pow_64(17));
    /// assert!(!i.is_divisible_2pow_64(18));
    /// ```
    fn is_divisible_2pow_64(&self, b: u64) -> bool;

    /// Returns [`true`] if the number is congruent to <i>c</i> mod
    /// <i>divisor</i>, that is, if there exists a <i>q</i> such that `self` =
    /// <i>c</i> + <i>q</i> × <i>divisor</i>. Unlike other division functions,
    /// `divisor` can be zero.
    ///
    /// This method is similar to [`is_congruent_u`][Integer::is_congruent_u]
    /// but takes `c` and the divisor as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let n = Integer::from(105);
    /// assert!(n.is_congruent_u64(3335, 10));
    /// assert!(!n.is_congruent_u64(107, 10));
    /// // n is congruent to itself if divisor is 0
    /// assert!(n.is_congruent_u64(105, 0));
    /// ```
    fn is_congruent_u64(&self, c: u64, divisor: u64) -> bool;

    /// Returns [`true`] if the number is congruent to <i>c</i> mod
    /// 2<sup><i>b</i></sup>, that is, if there exists a <i>q</i> such that
    /// `self` = <i>c</i> + <i>q</i> × 2<sup><i>b</i></sup>.
    ///
    /// This method is similar to
    /// [`is_congruent_2pow`][Integer::is_congruent_2pow] but takes `b` as
    /// [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let n = Integer::from(13 << 17 | 21);
    /// assert!(n.is_congruent_2pow_64(&Integer::from(7 << 17 | 21), 17));
    /// assert!(!n.is_congruent_2pow_64(&Integer::from(13 << 17 | 22), 17));
    /// ```
    fn is_congruent_2pow_64(&self, c: &Self, b: u64) -> bool;

    /// Returns the number of bits required to represent the absolute value.
    ///
    /// This method is similar to
    /// [`significant_bits`][Integer::significant_bits] but returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    ///
    /// assert_eq!(Integer::from(0).significant_bits_64(), 0);  //    “”
    /// assert_eq!(Integer::from(1).significant_bits_64(), 1);  //   “1”
    /// assert_eq!(Integer::from(4).significant_bits_64(), 3);  // “100”
    /// assert_eq!(Integer::from(7).significant_bits_64(), 3);  // “111”
    /// assert_eq!(Integer::from(-1).significant_bits_64(), 1); //   “1”
    /// assert_eq!(Integer::from(-4).significant_bits_64(), 3); // “100”
    /// assert_eq!(Integer::from(-7).significant_bits_64(), 3); // “111”
    /// ```
    fn significant_bits_64(&self) -> u64;

    /// Returns the number of bits required to represent the value using a
    /// two’s-complement representation.
    ///
    /// For non-negative numbers, this method returns one more than
    /// the [`significant_bits_64`] method, since an extra zero is needed
    /// before the most significant bit.
    ///
    /// This method is similar to [`signed_bits`][Integer::signed_bits] but
    /// returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    ///
    /// assert_eq!(Integer::from(-5).signed_bits_64(), 4); // “1011”
    /// assert_eq!(Integer::from(-4).signed_bits_64(), 3); //  “100”
    /// assert_eq!(Integer::from(-3).signed_bits_64(), 3); //  “101”
    /// assert_eq!(Integer::from(-2).signed_bits_64(), 2); //   “10”
    /// assert_eq!(Integer::from(-1).signed_bits_64(), 1); //    “1”
    /// assert_eq!(Integer::from(0).signed_bits_64(), 1);  //    “0”
    /// assert_eq!(Integer::from(1).signed_bits_64(), 2);  //   “01”
    /// assert_eq!(Integer::from(2).signed_bits_64(), 3);  //  “010”
    /// assert_eq!(Integer::from(3).signed_bits_64(), 3);  //  “011”
    /// assert_eq!(Integer::from(4).signed_bits_64(), 4);  // “0100”
    /// ```
    ///
    /// [`significant_bits_64`]: Integer::significant_bits_64
    fn signed_bits_64(&self) -> u64;

    /// Returns the number of one bits if the value ≥ 0.
    ///
    /// This method is similar to [`count_ones`][Integer::count_ones] but
    /// returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// assert_eq!(Integer::from(0).count_ones_64(), Some(0));
    /// assert_eq!(Integer::from(15).count_ones_64(), Some(4));
    /// assert_eq!(Integer::from(-1).count_ones_64(), None);
    /// ```
    fn count_ones_64(&self) -> Option<u64>;

    /// Returns the number of zero bits if the value < 0.
    ///
    /// This method is similar to [`count_zeros`][Integer::count_zeros] but
    /// returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// assert_eq!(Integer::from(0).count_zeros_64(), None);
    /// assert_eq!(Integer::from(1).count_zeros_64(), None);
    /// assert_eq!(Integer::from(-1).count_zeros_64(), Some(0));
    /// assert_eq!(Integer::from(-2).count_zeros_64(), Some(1));
    /// assert_eq!(Integer::from(-7).count_zeros_64(), Some(2));
    /// assert_eq!(Integer::from(-8).count_zeros_64(), Some(3));
    /// ```
    fn count_zeros_64(&self) -> Option<u64>;

    /// Returns the location of the first zero, starting at `start`. If the bit
    /// at location `start` is zero, returns `start`.
    ///
    /// This method is similar to [`find_zero`][Integer::find_zero] but takes
    /// `start` as [`u64`] and returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// // -2 is ...11111110
    /// assert_eq!(Integer::from(-2).find_zero_64(0), Some(0));
    /// assert_eq!(Integer::from(-2).find_zero_64(1), None);
    /// // 15 is ...00001111
    /// assert_eq!(Integer::from(15).find_zero_64(0), Some(4));
    /// assert_eq!(Integer::from(15).find_zero_64(20), Some(20));
    /// ```
    fn find_zero_64(&self, start: u64) -> Option<u64>;

    /// Returns the location of the first one, starting at `start`. If the bit
    /// at location `start` is one, returns `start`.
    ///
    /// This method is similar to [`find_one`][Integer::find_one] but takes
    /// `start` as [`u64`] and returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// // 1 is ...00000001
    /// assert_eq!(Integer::from(1).find_one_64(0), Some(0));
    /// assert_eq!(Integer::from(1).find_one_64(1), None);
    /// // -16 is ...11110000
    /// assert_eq!(Integer::from(-16).find_one_64(0), Some(4));
    /// assert_eq!(Integer::from(-16).find_one_64(20), Some(20));
    /// ```
    fn find_one_64(&self, start: u64) -> Option<u64>;

    /// Sets the bit at location `index` to 1 if `val` is [`true`] or 0 if `val`
    /// is [`false`].
    ///
    /// This method is similar to [`set_bit`][Integer::set_bit] but takes
    /// `index` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(-1);
    /// assert_eq!(*i.set_bit_64(0, false), -2);
    /// i.assign(0xff);
    /// assert_eq!(*i.set_bit_64(11, true), 0x8ff);
    /// ```
    fn set_bit_64(&mut self, index: u64, val: bool) -> &mut Self;

    /// Returns [`true`] if the bit at location `index` is 1 or [`false`] if the
    /// bit is 0.
    ///
    /// This method is similar to [`get_bit`][Integer::get_bit] but takes
    /// `index` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(0b100101);
    /// assert!(i.get_bit_64(0));
    /// assert!(!i.get_bit_64(1));
    /// assert!(i.get_bit_64(5));
    /// let neg = Integer::from(-1);
    /// assert!(neg.get_bit_64(1000));
    /// ```
    fn get_bit_64(&self, index: u64) -> bool;

    /// Toggles the bit at location `index`.
    ///
    /// This method is similar to [`toggle_bit`][Integer::toggle_bit] but takes
    /// `index` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let mut i = Integer::from(0b100101);
    /// i.toggle_bit_64(5);
    /// assert_eq!(i, 0b101);
    /// ```
    fn toggle_bit_64(&mut self, index: u64) -> &mut Self;

    /// Retuns the Hamming distance if the two numbers have the same sign.
    ///
    /// The Hamming distance is the number of different bits.
    ///
    /// This method is similar to [`hamming_dist`][Integer::hamming_dist] but
    /// returns a [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// assert_eq!(Integer::from(0).hamming_dist_64(&i), None);
    /// assert_eq!(Integer::from(-1).hamming_dist_64(&i), Some(0));
    /// // -1 is ...11111111 and -13 is ...11110011
    /// assert_eq!(Integer::from(-13).hamming_dist_64(&i), Some(2));
    /// ```
    fn hamming_dist_64(&self, other: &Self) -> Option<u64>;

    /// Keeps the <i>n</i> least significant bits only, producing a result that
    /// is greater or equal to 0.
    ///
    /// This method is similar to [`keep_bits`][Integer::keep_bits] but takes
    /// `n` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// let keep_8 = i.keep_bits_64(8);
    /// assert_eq!(keep_8, 0xff);
    /// ```
    fn keep_bits_64(self, n: u64) -> Self;

    /// Keeps the <i>n</i> least significant bits only, producing a result that
    /// is greater or equal to 0.
    ///
    /// This method is similar to [`keep_bits_mut`][Integer::keep_bits_mut] but
    /// takes `n` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let mut i = Integer::from(-1);
    /// i.keep_bits_64_mut(8);
    /// assert_eq!(i, 0xff);
    /// ```
    fn keep_bits_64_mut(&mut self, n: u64);

    /// Keeps the <i>n</i> least significant bits only, producing a result that
    /// is greater or equal to 0.
    ///
    /// The following are implemented with the returned [incomplete-computation
    /// value][icv] as `Src`:
    ///   * <code>[Assign]\<Src> for [Integer]</code>
    ///   * <code>[From]\<Src> for [Integer]</code>
    ///   * <code>[Complete]\<[Completed][Complete::Completed] = [Integer]> for Src</code>
    ///
    /// This method is similar to [`keep_bits_ref`][Integer::keep_bits_ref] but
    /// takes `n` as [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// let r = i.keep_bits_64_ref(8);
    /// let eight_bits = Integer::from(r);
    /// assert_eq!(eight_bits, 0xff);
    /// ```
    ///
    /// [icv]: crate#incomplete-computation-values
    fn keep_bits_64_ref(&self, n: u64) -> KeepBitsIncomplete;

    /// Keeps the <i>n</i> least significant bits only, producing a negative
    /// result if the <i>n</i>th least significant bit is one.
    ///
    /// This method is similar to
    /// [`keep_signed_bits`][Integer::keep_signed_bits] but takes `n` as
    /// [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// let i_keep_8 = i.keep_signed_bits_64(8);
    /// assert_eq!(i_keep_8, -1);
    /// let j = Integer::from(15 << 8 | 15);
    /// let j_keep_8 = j.keep_signed_bits_64(8);
    /// assert_eq!(j_keep_8, 15);
    /// ```
    fn keep_signed_bits_64(self, n: u64) -> Self;

    /// Keeps the <i>n</i> least significant bits only, producing a negative
    /// result if the <i>n</i>th least significant bit is one.
    ///
    /// This method is similar to
    /// [`keep_signed_bits_mut`][Integer::keep_signed_bits_mut] but takes `n` as
    /// [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let mut i = Integer::from(-1);
    /// i.keep_signed_bits_64_mut(8);
    /// assert_eq!(i, -1);
    /// let mut j = Integer::from(15 << 8 | 15);
    /// j.keep_signed_bits_64_mut(8);
    /// assert_eq!(j, 15);
    /// ```
    fn keep_signed_bits_64_mut(&mut self, n: u64);

    /// Keeps the <i>n</i> least significant bits only, producing a negative
    /// result if the <i>n</i>th least significant bit is one.
    ///
    /// The following are implemented with the returned
    /// [incomplete-computation value][icv] as `Src`:
    ///   * <code>[Assign]\<Src> for [Integer]</code>
    ///   * <code>[From]\<Src> for [Integer]</code>
    ///   * <code>[Complete]\<[Completed][Complete::Completed] = [Integer]> for Src</code>
    ///
    /// This method is similar to
    /// [`keep_signed_bits_ref`][Integer::keep_signed_bits_ref] but takes `n` as
    /// [`u64`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::IntegerExt64;
    /// use rug::Integer;
    /// let i = Integer::from(-1);
    /// let r = i.keep_signed_bits_64_ref(8);
    /// let eight_bits = Integer::from(r);
    /// assert_eq!(eight_bits, -1);
    /// ```
    ///
    /// [icv]: crate#incomplete-computation-values
    fn keep_signed_bits_64_ref(&self, n: u64) -> KeepSignedBitsIncomplete<'_>;
}

impl IntegerExt64 for Integer {
    #[inline]
    fn to_f32_exp64(&self) -> (f32, u64) {
        let (f, exp) = self.to_f64_exp64();
        let trunc_f = misc::trunc_f64_to_f32(f);
        (trunc_f, exp)
    }

    #[inline]
    fn to_f64_exp64(&self) -> (f64, u64) {
        let (f, exp) = xmpz::get_f64_2exp(self);
        (f, exp.unwrapped_cast())
    }

    #[inline]
    fn is_divisible_u64(&self, divisor: u64) -> bool {
        xmpz::divisible_ui_p(self, divisor.unwrapped_cast())
    }

    #[inline]
    fn is_divisible_2pow_64(&self, b: u64) -> bool {
        xmpz::divisible_2exp_p(self, b.unwrapped_cast())
    }

    #[inline]
    fn is_congruent_u64(&self, c: u64, divisor: u64) -> bool {
        xmpz::congruent_ui_p(self, c.unwrapped_cast(), divisor.unwrapped_cast())
    }

    #[inline]
    fn is_congruent_2pow_64(&self, c: &Self, b: u64) -> bool {
        xmpz::congruent_2exp_p(self, c, b.unwrapped_cast())
    }

    #[inline]
    fn significant_bits_64(&self) -> u64 {
        xmpz::significant_bits(self).unwrapped_cast()
    }

    #[inline]
    fn signed_bits_64(&self) -> u64 {
        xmpz::signed_bits(self).unwrapped_cast()
    }

    #[inline]
    fn count_ones_64(&self) -> Option<u64> {
        xmpz::popcount(self).map(From::from)
    }

    #[inline]
    fn count_zeros_64(&self) -> Option<u64> {
        xmpz::zerocount(self).map(From::from)
    }

    #[inline]
    fn find_zero_64(&self, start: u64) -> Option<u64> {
        xmpz::scan0(self, start.unwrapped_cast()).map(From::from)
    }

    #[inline]
    fn find_one_64(&self, start: u64) -> Option<u64> {
        xmpz::scan1(self, start.unwrapped_cast()).map(From::from)
    }

    #[inline]
    fn set_bit_64(&mut self, index: u64, val: bool) -> &mut Self {
        if val {
            xmpz::setbit(self, index.unwrapped_cast());
        } else {
            xmpz::clrbit(self, index.unwrapped_cast());
        }
        self
    }

    #[inline]
    fn get_bit_64(&self, index: u64) -> bool {
        xmpz::tstbit(self, index.unwrapped_cast())
    }

    #[inline]
    fn toggle_bit_64(&mut self, index: u64) -> &mut Self {
        xmpz::combit(self, index.unwrapped_cast());
        self
    }

    #[inline]
    fn hamming_dist_64(&self, other: &Self) -> Option<u64> {
        xmpz::hamdist(self, other).map(From::from)
    }

    #[inline]
    #[must_use]
    fn keep_bits_64(mut self, n: u64) -> Self {
        self.keep_bits_64_mut(n);
        self
    }

    #[inline]
    fn keep_bits_64_mut(&mut self, n: u64) {
        xmpz::fdiv_r_2exp(self, (), n.unwrapped_cast())
    }

    #[inline]
    fn keep_bits_64_ref(&self, n: u64) -> KeepBitsIncomplete {
        let n = n.unwrapped_cast();
        KeepBitsIncomplete { ref_self: self, n }
    }

    #[inline]
    #[must_use]
    fn keep_signed_bits_64(mut self, n: u64) -> Self {
        self.keep_signed_bits_64_mut(n);
        self
    }

    #[inline]
    fn keep_signed_bits_64_mut(&mut self, n: u64) {
        xmpz::keep_signed_bits(self, (), n.unwrapped_cast());
    }

    #[inline]
    fn keep_signed_bits_64_ref(&self, n: u64) -> KeepSignedBitsIncomplete<'_> {
        let n = n.unwrapped_cast();
        KeepSignedBitsIncomplete { ref_self: self, n }
    }
}

ref_math_op1! { Integer; xmpz::fdiv_r_2exp; struct KeepBitsIncomplete { n: bitcnt_t } }
ref_math_op1! { Integer; xmpz::keep_signed_bits; struct KeepSignedBitsIncomplete { n: bitcnt_t } }
