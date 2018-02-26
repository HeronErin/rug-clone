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

//! Aribtrary-precision integers.
//!
//! This module provides support for arbitrary-precision integers of
//! type [`Integer`](../struct.Integer.html). Instances of `Integer`
//! always have a heap allocation for the bit data; if you want a
//! temporary small integer without heap allocation, you can use the
//! [`SmallInteger`](struct.SmallInteger.html) type.
//!
//! # Examples
//!
//! ```rust
//! use rug::{Assign, Integer};
//! use rug::integer::SmallInteger;
//! let mut int = Integer::from(10);
//! assert_eq!(int, 10);
//! let small = SmallInteger::from(-15);
//! // `small` behaves like an `Integer` in the following line:
//! int.assign(small.abs_ref());
//! assert_eq!(int, 15);
//! ```

mod arith;
pub(crate) mod big;
mod cmp;
mod division;
#[cfg(feature = "serde")]
mod serde;
pub(crate) mod small;
mod traits;

pub use integer::big::{IsPrime, ParseIntegerError};
pub use integer::small::SmallInteger;

#[cfg(test)]
mod tests {
    use {Assign, Integer};
    use gmp_mpfr_sys::gmp;
    use ops::NegAssign;
    use std::{f32, f64, i32, i64, u32, u64};
    use std::mem;

    #[test]
    fn check_int_conversions() {
        let mut i = Integer::from(-1);
        assert_eq!(i.to_u32_wrapping(), u32::MAX);
        assert_eq!(i.to_i32_wrapping(), -1);
        i.assign(0xff000000u32);
        i <<= 4;
        assert_eq!(i.to_u32_wrapping(), 0xf0000000u32);
        assert_eq!(i.to_i32_wrapping(), 0xf0000000u32 as i32);
        i = i.clone() << 32 | i;
        assert_eq!(i.to_u32_wrapping(), 0xf0000000u32);
        assert_eq!(i.to_i32_wrapping(), 0xf0000000u32 as i32);
        i.neg_assign();
        assert_eq!(i.to_u32_wrapping(), 0x10000000u32);
        assert_eq!(i.to_i32_wrapping(), 0x10000000i32);
    }

    #[test]
    fn check_option_conversion() {
        let mut i = Integer::new();
        assert_eq!(i.to_u32(), Some(0));
        assert_eq!(i.to_i32(), Some(0));
        assert_eq!(i.to_u64(), Some(0));
        assert_eq!(i.to_i64(), Some(0));
        i -= 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), Some(-1));
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), Some(-1));

        i.assign(i32::MIN);
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), Some(i32::MIN));
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), Some(i32::MIN as i64));
        i -= 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), Some(i32::MIN as i64 - 1));
        i.assign(i32::MAX);
        assert_eq!(i.to_u32(), Some(i32::MAX as u32));
        assert_eq!(i.to_i32(), Some(i32::MAX));
        assert_eq!(i.to_u64(), Some(i32::MAX as u64));
        assert_eq!(i.to_i64(), Some(i32::MAX as i64));
        i += 1;
        assert_eq!(i.to_u32(), Some(i32::MAX as u32 + 1));
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(i32::MAX as u64 + 1));
        assert_eq!(i.to_i64(), Some(i32::MAX as i64 + 1));
        i.assign(u32::MAX);
        assert_eq!(i.to_u32(), Some(u32::MAX));
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(u32::MAX as u64));
        assert_eq!(i.to_i64(), Some(u32::MAX as i64));
        i += 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(u32::MAX as u64 + 1));
        assert_eq!(i.to_i64(), Some(u32::MAX as i64 + 1));

        i.assign(i64::MIN);
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), Some(i64::MIN));
        i -= 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), None);
        i.assign(i64::MAX);
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(i64::MAX as u64));
        assert_eq!(i.to_i64(), Some(i64::MAX));
        i += 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(i64::MAX as u64 + 1));
        assert_eq!(i.to_i64(), None);
        i.assign(u64::MAX);
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), Some(u64::MAX));
        assert_eq!(i.to_i64(), None);
        i += 1;
        assert_eq!(i.to_u32(), None);
        assert_eq!(i.to_i32(), None);
        assert_eq!(i.to_u64(), None);
        assert_eq!(i.to_i64(), None);
    }

    #[test]
    fn check_float_conversions() {
        let mut i = Integer::from(0);
        assert_eq!(i.to_f32(), 0.0);
        assert_eq!(i.to_f64(), 0.0);
        i.assign(0xff);
        assert_eq!(i.to_f32(), 255.0);
        assert_eq!(i.to_f64(), 255.0);
        i <<= 80;
        assert_eq!(i.to_f32(), 255.0 * 2f32.powi(80));
        assert_eq!(i.to_f64(), 255.0 * 2f64.powi(80));
        i = i.clone() << 30 | i;
        assert_eq!(i.to_f32(), 255.0 * 2f32.powi(110));
        assert_eq!(
            i.to_f64(),
            255.0 * (2f64.powi(80) + 2f64.powi(110))
        );
        i <<= 100;
        assert_eq!(i.to_f32(), f32::INFINITY);
        assert_eq!(
            i.to_f64(),
            255.0 * (2f64.powi(180) + 2f64.powi(210))
        );
        i <<= 1000;
        assert_eq!(i.to_f32(), f32::INFINITY);
        assert_eq!(i.to_f64(), f64::INFINITY);
        i.assign(-0xff_ffff);
        assert_eq!(i.to_f32(), -0xff_ffff as f32);
        assert_eq!(i.to_f64(), -0xff_ffff as f64);
        i.assign(-0xfff_ffff);
        assert_eq!(i.to_f32(), -0xfff_fff0 as f32);
        assert_eq!(i.to_f64(), -0xfff_ffff as f64);
    }

    #[test]
    fn check_from_str() {
        let mut i: Integer = "+134".parse().unwrap();
        assert_eq!(i, 134);
        i.assign(
            Integer::parse_radix("-ffFFffffFfFfffffffffffffffffffff", 16)
                .unwrap(),
        );
        assert_eq!(i.significant_bits(), 128);
        i -= 1;
        assert_eq!(i.significant_bits(), 129);

        let bad_strings = [
            ("_1", None),
            ("+_1", None),
            ("-_1", None),
            ("+-3", None),
            ("-+3", None),
            ("++3", None),
            ("--3", None),
            ("0+3", None),
            ("", None),
            ("9\09", None),
            ("80", Some(8)),
            ("0xf", Some(16)),
            ("9", Some(9)),
            ("/0", Some(36)),
            (":0", Some(36)),
            ("@0", Some(36)),
            ("[0", Some(36)),
            ("`0", Some(36)),
            ("{0", Some(36)),
            ("Z0", Some(35)),
            ("z0", Some(35)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(
                Integer::parse_radix(s, radix.unwrap_or(10)).is_err(),
                "{} parsed correctly",
                s
            );
        }
        let good_strings = [
            ("0", 10, 0),
            ("+0", 16, 0),
            ("  + 1_2", 10, 12),
            ("  - 1_2", 10, -12),
            ("-0", 2, 0),
            ("99", 10, 99),
            ("+Cc", 16, 0xcc),
            ("-77", 8, -0o77),
            (" 1 2\n 3 4 ", 10, 1234),
            ("1_2__", 10, 12),
            ("z0", 36, 35 * 36),
            ("Z0", 36, 35 * 36),
        ];
        for &(s, radix, i) in good_strings.into_iter() {
            match Integer::parse_radix(s, radix) {
                Ok(ok) => assert_eq!(Integer::from(ok), i),
                Err(_) => panic!("could not parse {}", s),
            }
        }
    }

    #[test]
    fn check_formatting() {
        let i = Integer::from(-11);
        assert_eq!(format!("{}", i), "-11");
        assert_eq!(format!("{:?}", i), "-11");
        assert_eq!(format!("{:b}", i), "-1011");
        assert_eq!(format!("{:#b}", i), "-0b1011");
        assert_eq!(format!("{:o}", i), "-13");
        assert_eq!(format!("{:#o}", i), "-0o13");
        assert_eq!(format!("{:x}", i), "-b");
        assert_eq!(format!("{:X}", i), "-B");
        assert_eq!(format!("{:8x}", i), "      -b");
        assert_eq!(format!("{:08X}", i), "-000000B");
        assert_eq!(format!("{:#08x}", i), "-0x0000b");
        assert_eq!(format!("{:#8X}", i), "    -0xB");
    }

    #[test]
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(
            gmp::NUMB_BITS as usize,
            8 * mem::size_of::<gmp::limb_t>()
        );

        // we check that we have either 64 or 32, but not both
        assert!(cfg!(gmp_limb_bits_64) != cfg!(gmp_limb_bits_32));

        // check that target_pointer_width is 32 or 64
        #[cfg(not(any(target_pointer_width = "32",
                      target_pointer_width = "64")))]
        panic!("target_pointer_width is not 32 or 64");
    }

    #[cfg(gmp_limb_bits_64)]
    #[test]
    fn check_limbs() {
        assert_eq!(gmp::NUMB_BITS, 64);
    }

    #[cfg(gmp_limb_bits_32)]
    #[test]
    fn check_limbs() {
        assert_eq!(gmp::NUMB_BITS, 32);
    }
}
