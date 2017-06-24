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

mod small_integer;

pub use big_integer::{IsPrime, ParseIntegerError, ValidInteger};
pub use integer::small_integer::SmallInteger;

#[cfg(test)]
mod tests {
    use {Assign, Integer};
    use gmp_mpfr_sys::gmp;
    use ops::{NegAssign, Pow};
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
                assert_eq!(b.clone() + op, b.clone() + &iop);
                assert_eq!(b.clone() - op, b.clone() - &iop);
                assert_eq!(b.clone() * op, b.clone() * &iop);
                if op != 0 {
                    assert_eq!(b.clone() / op, b.clone() / &iop);
                    assert_eq!(b.clone() % op, b.clone() % &iop);
                }
                assert_eq!(b.clone() & op, b.clone() & &iop);
                assert_eq!(b.clone() | op, b.clone() | &iop);
                assert_eq!(b.clone() ^ op, b.clone() ^ &iop);
                assert_eq!(op + b.clone(), iop.clone() + &b);
                assert_eq!(op - b.clone(), iop.clone() - &b);
                assert_eq!(op * b.clone(), iop.clone() * &b);
                if b.sign() != Ordering::Equal {
                    assert_eq!(op / b.clone(), iop.clone() / &b);
                    assert_eq!(op % b.clone(), iop.clone() % &b);
                }
                assert_eq!(op & b.clone(), iop.clone() & &b);
                assert_eq!(op | b.clone(), iop.clone() | &b);
                assert_eq!(op ^ b.clone(), iop.clone() ^ &b);
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                assert_eq!(b.clone() + op, b.clone() + &iop);
                assert_eq!(b.clone() - op, b.clone() - &iop);
                assert_eq!(b.clone() * op, b.clone() * &iop);
                if op != 0 {
                    assert_eq!(b.clone() / op, b.clone() / &iop);
                    assert_eq!(b.clone() % op, b.clone() % &iop);
                }
                assert_eq!(b.clone() & op, b.clone() & &iop);
                assert_eq!(b.clone() | op, b.clone() | &iop);
                assert_eq!(b.clone() ^ op, b.clone() ^ &iop);
                assert_eq!(op + b.clone(), iop.clone() + &b);
                assert_eq!(op - b.clone(), iop.clone() - &b);
                assert_eq!(op * b.clone(), iop.clone() * &b);
                if b.sign() != Ordering::Equal {
                    assert_eq!(op / b.clone(), iop.clone() / &b);
                    assert_eq!(op % b.clone(), iop.clone() % &b);
                }
                assert_eq!(op & b.clone(), iop.clone() & &b);
                assert_eq!(op | b.clone(), iop.clone() | &b);
                assert_eq!(op ^ b.clone(), iop.clone() ^ &b);
            }
        }
    }

    #[test]
    fn check_ref_op() {
        let lhs = Integer::from(0x00ff);
        let rhs = Integer::from(0x0f0f);
        let pu = 30_u32;
        let pi = -15_i32;
        assert_eq!(Integer::from(-&lhs), -lhs.clone());
        assert_eq!(Integer::from(&lhs + &rhs), lhs.clone() + &rhs);
        assert_eq!(Integer::from(&lhs - &rhs), lhs.clone() - &rhs);
        assert_eq!(Integer::from(&lhs * &rhs), lhs.clone() * &rhs);
        assert_eq!(Integer::from(&lhs / &rhs), lhs.clone() / &rhs);
        assert_eq!(Integer::from(&lhs % &rhs), lhs.clone() % &rhs);
        assert_eq!(Integer::from(!&lhs), !lhs.clone());
        assert_eq!(Integer::from(&lhs & &rhs), lhs.clone() & &rhs);
        assert_eq!(Integer::from(&lhs | &rhs), lhs.clone() | &rhs);
        assert_eq!(Integer::from(&lhs ^ &rhs), lhs.clone() ^ &rhs);

        assert_eq!(Integer::from(&lhs + pu), lhs.clone() + pu);
        assert_eq!(Integer::from(&lhs - pu), lhs.clone() - pu);
        assert_eq!(Integer::from(&lhs * pu), lhs.clone() * pu);
        assert_eq!(Integer::from(&lhs / pu), lhs.clone() / pu);
        assert_eq!(Integer::from(&lhs % pu), lhs.clone() % pu);
        assert_eq!(Integer::from(&lhs & pu), lhs.clone() & pu);
        assert_eq!(Integer::from(&lhs | pu), lhs.clone() | pu);
        assert_eq!(Integer::from(&lhs ^ pu), lhs.clone() ^ pu);
        assert_eq!(Integer::from(&lhs << pu), lhs.clone() << pu);
        assert_eq!(Integer::from(&lhs >> pu), lhs.clone() >> pu);
        assert_eq!(Integer::from((&lhs).pow(pu)), lhs.clone().pow(pu));

        assert_eq!(Integer::from(&lhs + pi), lhs.clone() + pi);
        assert_eq!(Integer::from(&lhs - pi), lhs.clone() - pi);
        assert_eq!(Integer::from(&lhs * pi), lhs.clone() * pi);
        assert_eq!(Integer::from(&lhs / pi), lhs.clone() / pi);
        assert_eq!(Integer::from(&lhs % pi), lhs.clone() % pi);
        assert_eq!(Integer::from(&lhs & pi), lhs.clone() & pi);
        assert_eq!(Integer::from(&lhs | pi), lhs.clone() | pi);
        assert_eq!(Integer::from(&lhs ^ pi), lhs.clone() ^ pi);
        assert_eq!(Integer::from(&lhs << pi), lhs.clone() << pi);
        assert_eq!(Integer::from(&lhs >> pi), lhs.clone() >> pi);

        assert_eq!(Integer::from(pu + &lhs), pu + lhs.clone());
        assert_eq!(Integer::from(pu - &lhs), pu - lhs.clone());
        assert_eq!(Integer::from(pu * &lhs), pu * lhs.clone());
        assert_eq!(Integer::from(pu / &lhs), pu / lhs.clone());
        assert_eq!(Integer::from(pu % &lhs), pu % lhs.clone());
        assert_eq!(Integer::from(pu & &lhs), pu & lhs.clone());
        assert_eq!(Integer::from(pu | &lhs), pu | lhs.clone());
        assert_eq!(Integer::from(pu ^ &lhs), pu ^ lhs.clone());

        assert_eq!(Integer::from(pi + &lhs), pi + lhs.clone());
        assert_eq!(Integer::from(pi - &lhs), pi - lhs.clone());
        assert_eq!(Integer::from(pi * &lhs), pi * lhs.clone());
        assert_eq!(Integer::from(pi / &lhs), pi / lhs.clone());
        assert_eq!(Integer::from(pi % &lhs), pi % lhs.clone());
        assert_eq!(Integer::from(pi & &lhs), pi & lhs.clone());
        assert_eq!(Integer::from(pi | &lhs), pi | lhs.clone());
        assert_eq!(Integer::from(pi ^ &lhs), pi ^ lhs.clone());
    }

    #[test]
    fn check_shift_u_s() {
        let pos: Integer = Integer::from(11) << 100;
        let neg: Integer = Integer::from(-33) << 50;
        assert_eq!(pos.clone() << 10, pos.clone() >> -10);
        assert_eq!(pos.clone() << 10, Integer::from(11) << 110);
        assert_eq!(pos.clone() << -100, pos.clone() >> 100);
        assert_eq!(pos.clone() << -100, 11);
        assert_eq!(neg.clone() << 10, neg.clone() >> -10);
        assert_eq!(neg.clone() << 10, Integer::from(-33) << 60);
        assert_eq!(neg.clone() << -100, neg.clone() >> 100);
        assert_eq!(neg.clone() << -100, -1);
    }

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
        assert_eq!(i.to_f64(), 255.0 * (2f64.powi(80) + 2f64.powi(110)));
        i <<= 100;
        assert_eq!(i.to_f32(), f32::INFINITY);
        assert_eq!(i.to_f64(), 255.0 * (2f64.powi(180) + 2f64.powi(210)));
        i <<= 1000;
        assert_eq!(i.to_f32(), f32::INFINITY);
        assert_eq!(i.to_f64(), f64::INFINITY);
        i.assign(-0xff_ffff);
        assert_eq!(i.to_f32(), -0xff_ffff as f32);
        assert_eq!(i.to_f64(), -0xff_ffff as f64);
        i.assign(-0xfff_ffff);
        assert_eq!(i.to_f32(), -0xff_ffff0 as f32);
        assert_eq!(i.to_f64(), -0xff_fffff as f64);
    }

    #[test]
    fn check_from_str() {
        let mut i: Integer = "+134".parse().unwrap();
        assert_eq!(i, 134);
        i.assign_str_radix("-ffFFffffFfFfffffffffffffffffffff", 16)
            .unwrap();
        assert_eq!(i.significant_bits(), 128);
        i -= 1;
        assert_eq!(i.significant_bits(), 129);

        let bad_strings = [
            ("1\0", None),
            ("1_2", None),
            (" 1", None),
            ("+-3", None),
            ("-+3", None),
            ("++3", None),
            ("--3", None),
            ("0+3", None),
            ("0 ", None),
            ("", None),
            ("80", Some(8)),
            ("0xf", Some(16)),
            ("9", Some(9)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Integer::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings = [
            ("0", 10, 0),
            ("+0", 16, 0),
            ("-0", 2, 0),
            ("99", 10, 99),
            ("+Cc", 16, 0xcc),
            ("-77", 8, -0o77),
        ];
        for &(s, radix, i) in good_strings.into_iter() {
            assert_eq!(Integer::from_str_radix(s, radix).unwrap(), i);
        }
    }

    #[test]
    fn check_formatting() {
        let i = Integer::from((-11));
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
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
        // we assume that a limb has 32 or 64 bits.
        assert!(gmp::NUMB_BITS == 32 || gmp::NUMB_BITS == 64);
    }
}
