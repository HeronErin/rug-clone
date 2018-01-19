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

//! Multi-precision floating-point numbers with correct rounding.
//!
//! This module provides support for floating-point numbers of type
//! [`Float`](../struct.Float.html).

pub(crate) mod arith;
pub(crate) mod big;
mod cmp;
mod ord;
#[cfg(feature = "serde")]
mod serde;
pub(crate) mod small;
mod traits;

use cast::cast;
pub use float::big::{ParseFloatError, ValidFloat};
pub use float::ord::OrdFloat;
pub use float::small::SmallFloat;
use gmp_mpfr_sys::mpfr;
use std::{i32, u32};
use std::mem;

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
    if min > mpfr::exp_t::from(i32::MIN) {
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
    if max < mpfr::exp_t::from(i32::MAX) {
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
    cast(mpfr::PREC_MIN)
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
    if mem::size_of::<mpfr::prec_t>() <= mem::size_of::<u32>()
        || max < cast::<_, mpfr::prec_t>(u32::MAX)
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
/// use rug::Float;
/// use rug::float::Round;
/// use rug::ops::AssignRound;
/// let mut f4 = Float::new(4);
/// f4.assign_round(10.4, Round::Nearest);
/// assert_eq!(f4, 10);
/// f4.assign_round(10.6, Round::Nearest);
/// assert_eq!(f4, 11);
/// f4.assign_round(-10.7, Round::Zero);
/// assert_eq!(f4, -10);
/// f4.assign_round(10.3, Round::Up);
/// assert_eq!(f4, 11);
/// ```
///
/// Rounding to the nearest will round numbers exactly between two
/// representable numbers to the even one.
///
/// ```rust
/// use rug::Float;
/// use rug::float::Round;
/// use rug::ops::AssignRound;
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
#[allow(deprecated)]
pub enum Round {
    /// Round towards the nearest.
    Nearest,
    /// Round towards zero.
    Zero,
    /// Round towards plus infinity.
    Up,
    /// Round towards minus infinity.
    Down,
    #[deprecated(since = "0.9.2", note = "not supported at the moment")]
    #[doc(hidden)]
    AwayFromZero,
}

impl Default for Round {
    #[inline]
    fn default() -> Round {
        Round::Nearest
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
/// use rug::float::Special;
///
/// let zero = Float::with_val(53, Special::Zero);
/// let neg_zero = Float::with_val(53, Special::NegZero);
/// let infinity = Float::with_val(53, Special::Infinity);
/// let neg_infinity = Float::with_val(53, Special::NegInfinity);
/// let nan = Float::with_val(53, Special::Nan);
///
/// assert_eq!(zero, 0);
/// assert!(zero.is_sign_positive());
/// assert_eq!(neg_zero, 0);
/// assert!(neg_zero.is_sign_negative());
/// assert!(infinity.is_infinite());
/// assert!(infinity.is_sign_positive());
/// assert!(neg_infinity.is_infinite());
/// assert!(neg_infinity.is_sign_negative());
/// assert!(nan.is_nan());
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Special {
    /// Positive zero.
    Zero,
    /// Negative zero.
    NegZero,
    /// Positive infinity.
    Infinity,
    /// Negative infinity.
    NegInfinity,
    /// Not a number.
    Nan,
}

#[cfg(test)]
mod tests {
    use {Assign, Float};
    use float::{Round, Special};
    use gmp_mpfr_sys::{gmp, mpfr};
    use std::cmp::Ordering;
    use std::f64;
    use std::mem;

    #[test]
    fn check_from_str() {
        assert!(Float::from_str_radix("-@nan@", 2, 53).unwrap().is_nan());
        assert!(Float::from_str("-0", 53).unwrap().is_sign_negative());
        assert!(Float::from_str("+0", 53).unwrap().is_sign_positive());
        assert!(Float::from_str("1e1000", 53).unwrap().is_finite());
        let huge_hex = "1@99999999999999999999999999999999";
        assert!(
            Float::from_str_radix(huge_hex, 16, 53)
                .unwrap()
                .is_infinite()
        );

        let bad_strings = [
            ("inf", 16),
            ("1.1.", 10),
            ("1e", 10),
            ("e10", 10),
            (".e10", 10),
            ("1e1.", 10),
            ("1e1e1", 10),
            ("1e+-1", 10),
            ("1e-+1", 10),
            ("+-1", 10),
            ("-+1", 10),
            ("infinit", 10),
            ("1@1a", 16),
            ("9", 9),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Float::valid_str_radix(s, radix).is_err());
        }
        let good_strings = [
            ("INF", 10, f64::INFINITY),
            ("-@iNf@", 16, f64::NEG_INFINITY),
            ("+0e99", 2, 0.0),
            ("-9.9e1", 10, -99.0),
            ("-.99e+2", 10, -99.0),
            ("+99.e+0", 10, 99.0),
            ("-99@-1", 10, -9.9f64),
            ("-abc.DEF@3", 16, -0xabcdef as f64),
            ("1e1023", 2, 2.0f64.powi(1023)),
        ];
        for &(s, radix, f) in good_strings.into_iter() {
            assert_eq!(Float::from_str_radix(s, radix, 53).unwrap(), f);
        }
    }

    #[test]
    fn check_clamping() {
        let mut f = Float::new(4);

        f.assign(-1);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Down);
        assert_eq!(f, 1.0);
        assert_eq!(dir, Ordering::Less);

        f.assign(-1);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Up);
        assert_eq!(f, 1.125);
        assert_eq!(dir, Ordering::Greater);

        f.assign(2);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Down);
        assert_eq!(f, 1.0);
        assert_eq!(dir, Ordering::Less);

        f.assign(2);
        let dir = f.clamp_round(&1.00002, &1.00001, Round::Up);
        assert_eq!(f, 1.125);
        assert_eq!(dir, Ordering::Greater);
    }

    #[test]
    #[should_panic(expected = "minimum larger than maximum")]
    fn check_clamping_panic() {
        let mut f = Float::new(4);
        f.assign(-1);
        f.clamp(&1.00001, &0.99999);
    }

    #[test]
    fn check_formatting() {
        let mut f = Float::with_val(53, Special::Zero);
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "0.0");
        assert_eq!(format!("{:+?}", f), "+0.0");
        f.assign(Special::NegZero);
        assert_eq!(format!("{}", f), "-0.0");
        assert_eq!(format!("{:?}", f), "-0.0");
        assert_eq!(format!("{:+?}", f), "-0.0");
        f.assign(Special::Infinity);
        assert_eq!(format!("{}", f), "inf");
        assert_eq!(format!("{:+}", f), "+inf");
        assert_eq!(format!("{:x}", f), "@inf@");
        f.assign(Special::NegInfinity);
        assert_eq!(format!("{}", f), "-inf");
        assert_eq!(format!("{:x}", f), "-@inf@");
        f.assign(Special::Nan);
        assert_eq!(format!("{}", f), "NaN");
        assert_eq!(format!("{:+}", f), "+NaN");
        assert_eq!(format!("{:x}", f), "@NaN@");
        f = -f;
        assert_eq!(format!("{}", f), "-NaN");
        assert_eq!(format!("{:x}", f), "-@NaN@");
        f.assign(-27);
        assert_eq!(format!("{:.2}", f), "-2.7e1");
        assert_eq!(format!("{:.4?}", f), "-2.700e1");
        assert_eq!(format!("{:.4e}", f), "-2.700e1");
        assert_eq!(format!("{:.4E}", f), "-2.700E1");
        assert_eq!(format!("{:.8b}", f), "-1.1011000e4");
        assert_eq!(format!("{:.3b}", f), "-1.11e4");
        assert_eq!(format!("{:#.8b}", f), "-0b1.1011000e4");
        assert_eq!(format!("{:.2o}", f), "-3.3e1");
        assert_eq!(format!("{:#.2o}", f), "-0o3.3e1");
        assert_eq!(format!("{:.2x}", f), "-1.b@1");
        assert_eq!(format!("{:.2X}", f), "-1.B@1");
        assert_eq!(format!("{:12.1x}", f), "      -1.b@1");
        assert_eq!(format!("{:012.3X}", f), "-000001.B0@1");
        assert_eq!(format!("{:#012.2x}", f), "-0x00001.b@1");
        assert_eq!(format!("{:#12.2X}", f), "    -0x1.B@1");
    }

    #[test]
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
        assert_eq!(unsafe { mpfr::custom_get_size(64) }, 8);
        assert!(
            unsafe { mpfr::custom_get_size(32) } <= gmp::NUMB_BITS as usize
        );
    }
}
