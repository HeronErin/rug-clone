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
use crate::Integer;
use az::UnwrappedCast;

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
}
