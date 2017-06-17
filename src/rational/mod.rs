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

//! TODO: document mod `rational`

mod big_rational;
mod small_rational;
mod xgmp;

pub use self::big_rational::{MutNumerDenom, ParseRationalError, Rational,
                             ValidRational};
pub use self::small_rational::SmallRational;

#[cfg(test)]
mod tests {
    use gmp_mpfr_sys::gmp;
    use ops::Pow;
    use rational::Rational;
    use std::{i32, u32};
    use std::cmp::Ordering;
    use std::mem;

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
