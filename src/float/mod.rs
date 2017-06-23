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

//! Multi-precision floating-point numbers with correct rounding.
//!
//! This module provides floating-point numbers with arbitrarily large
//! precision, and with correct rounding. The rounding method of the
//! required operations can be specified, and the direction of the
//! rounding is returned.
//!
//! # Examples
//!
//! ```rust
//! use rug::Float;
//! use rug::float::Round;
//! use rug::ops::DivRound;
//! use std::cmp::Ordering;
//! // A precision of 32 significant bits is specified here.
//! // (The primitive `f32` has a precision of 24 and
//! // `f64` has a precision of 53.)
//! let mut two_thirds_down = Float::with_val(32, 2.0);
//! let dir = two_thirds_down.div_round(3.0, Round::Down);
//! // since we rounded down, direction is Ordering::Less
//! assert_eq!(dir, Ordering::Less);
//! let mut two_thirds_up = Float::with_val(32, 2.0);
//! let dir = two_thirds_up.div_round(3.0, Round::Up);
//! // since we rounded up, direction is Ordering::Greater
//! assert_eq!(dir, Ordering::Greater);
//! let diff_expected = 2.0_f64.powi(-32);
//! let diff = two_thirds_up - two_thirds_down;
//! assert_eq!(diff, diff_expected);
//! ```

mod big_float;
mod small_float;
mod xmpfr;

pub use self::big_float::{Constant, Float, ParseFloatError, Round, Special,
                          ValidFloat, exp_max, exp_min, prec_max, prec_min};
pub use self::small_float::SmallFloat;

#[cfg(test)]
mod tests {
    use float::{Float, Special};
    use gmp_mpfr_sys::{gmp, mpfr};
    use integer::Integer;
    use ops::{Assign, Pow};
    #[cfg(feature = "rational")]
    use rational::Rational;
    use std::{f32, f64, i32, u32};
    use std::mem;
    use std::str::FromStr;

    fn same(a: Float, b: Float) -> bool {
        if a.is_nan() && b.is_nan() {
            return true;
        }
        if a == b {
            return true;
        }
        if a.prec() == b.prec() {
            return false;
        }
        a == Float::with_val(a.prec(), b)
    }

    #[test]
    fn check_ref_op() {
        let lhs = Float::with_val(53, 12.25);
        let rhs = Float::with_val(53, -1.375);
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Float::with_val(53, -&lhs), -lhs.clone());
        assert_eq!(Float::with_val(53, &lhs + &rhs), lhs.clone() + &rhs);
        assert_eq!(Float::with_val(53, &lhs - &rhs), lhs.clone() - &rhs);
        assert_eq!(Float::with_val(53, &lhs * &rhs), lhs.clone() * &rhs);
        assert_eq!(Float::with_val(53, &lhs / &rhs), lhs.clone() / &rhs);
        assert_eq!(
            Float::with_val(53, (&lhs).pow(&rhs)),
            lhs.clone().pow(&rhs)
        );

        assert_eq!(Float::with_val(53, &lhs + pu), lhs.clone() + pu);
        assert_eq!(Float::with_val(53, &lhs - pu), lhs.clone() - pu);
        assert_eq!(Float::with_val(53, &lhs * pu), lhs.clone() * pu);
        assert_eq!(Float::with_val(53, &lhs / pu), lhs.clone() / pu);
        assert_eq!(Float::with_val(53, &lhs << pu), lhs.clone() << pu);
        assert_eq!(Float::with_val(53, &lhs >> pu), lhs.clone() >> pu);
        assert_eq!(Float::with_val(53, (&lhs).pow(pu)), lhs.clone().pow(pu));

        assert_eq!(Float::with_val(53, pu + &lhs), pu + lhs.clone());
        assert_eq!(Float::with_val(53, pu - &lhs), pu - lhs.clone());
        assert_eq!(Float::with_val(53, pu * &lhs), pu * lhs.clone());
        assert_eq!(Float::with_val(53, pu / &lhs), pu / lhs.clone());
        assert_eq!(
            Float::with_val(53, Pow::pow(pu, &lhs)),
            Pow::pow(pu, lhs.clone())
        );

        assert_eq!(Float::with_val(53, &lhs + pi), lhs.clone() + pi);
        assert_eq!(Float::with_val(53, &lhs - pi), lhs.clone() - pi);
        assert_eq!(Float::with_val(53, &lhs * pi), lhs.clone() * pi);
        assert_eq!(Float::with_val(53, &lhs / pi), lhs.clone() / pi);
        assert_eq!(Float::with_val(53, &lhs << pi), lhs.clone() << pi);
        assert_eq!(Float::with_val(53, &lhs >> pi), lhs.clone() >> pi);
        assert_eq!(Float::with_val(53, (&lhs).pow(pi)), lhs.clone().pow(pi));

        assert_eq!(Float::with_val(53, pi + &lhs), pi + lhs.clone());
        assert_eq!(Float::with_val(53, pi - &lhs), pi - lhs.clone());
        assert_eq!(Float::with_val(53, pi * &lhs), pi * lhs.clone());
        assert_eq!(Float::with_val(53, pi / &lhs), pi / lhs.clone());

        assert_eq!(Float::with_val(53, &lhs + ps), lhs.clone() + ps);
        assert_eq!(Float::with_val(53, &lhs - ps), lhs.clone() - ps);
        assert_eq!(Float::with_val(53, &lhs * ps), lhs.clone() * ps);
        assert_eq!(Float::with_val(53, &lhs / ps), lhs.clone() / ps);

        assert_eq!(Float::with_val(53, ps + &lhs), ps + lhs.clone());
        assert_eq!(Float::with_val(53, ps - &lhs), ps - lhs.clone());
        assert_eq!(Float::with_val(53, ps * &lhs), ps * lhs.clone());
        assert_eq!(Float::with_val(53, ps / &lhs), ps / lhs.clone());

        assert_eq!(Float::with_val(53, &lhs + pd), lhs.clone() + pd);
        assert_eq!(Float::with_val(53, &lhs - pd), lhs.clone() - pd);
        assert_eq!(Float::with_val(53, &lhs * pd), lhs.clone() * pd);
        assert_eq!(Float::with_val(53, &lhs / pd), lhs.clone() / pd);

        assert_eq!(Float::with_val(53, pd + &lhs), pd + lhs.clone());
        assert_eq!(Float::with_val(53, pd - &lhs), pd - lhs.clone());
        assert_eq!(Float::with_val(53, pd * &lhs), pd * lhs.clone());
        assert_eq!(Float::with_val(53, pd / &lhs), pd / lhs.clone());
    }

    #[test]
    fn check_arith_others() {
        let work_prec = 20;
        let check_prec = 100;
        let f = [
            Float::with_val(work_prec, Special::Zero),
            Float::with_val(work_prec, Special::MinusZero),
            Float::with_val(work_prec, Special::Infinity),
            Float::with_val(work_prec, Special::MinusInfinity),
            Float::with_val(work_prec, Special::Nan),
            Float::with_val(work_prec, 1),
            Float::with_val(work_prec, -1),
            Float::with_val(work_prec, 999999e100),
            Float::with_val(work_prec, 999999e-100),
            Float::with_val(work_prec, -999999e100),
            Float::with_val(work_prec, -999999e-100),
        ];
        let z = [
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        #[cfg(feature = "rational")]
        let q = [
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];
        let u = [0, 1, 1000, u32::MAX];
        let s = [i32::MIN, -1000, -1, 0, 1, 1000, i32::MAX];
        let double = [
            f64::INFINITY,
            f64::MAX,
            f64::MIN_POSITIVE,
            0.0,
            -0.0,
            -f64::MIN_POSITIVE,
            f64::MIN,
            f64::NEG_INFINITY,
            f64::NAN,
            1.0,
            2.0,
            12.0e43,
        ];
        let single = [
            f32::INFINITY,
            f32::MAX,
            f32::MIN_POSITIVE,
            0.0,
            -0.0,
            -f32::MIN_POSITIVE,
            f32::MIN,
            f32::NEG_INFINITY,
            f32::NAN,
            1.0,
            2.0,
            12.0e30,
        ];
        for zz in &z {
            let zf = Float::with_val(check_prec, zz);
            for ff in &f {
                assert!(same(ff.clone() + zz, ff.clone() + &zf));
                assert!(same(ff.clone() - zz, ff.clone() - &zf));
                assert!(same(ff.clone() * zz, ff.clone() * &zf));
                assert!(same(ff.clone() / zz, ff.clone() / &zf));
                assert!(same(zz.clone() + ff.clone(), zf.clone() + ff));
                assert!(same(zz.clone() - ff.clone(), zf.clone() - ff));
                assert!(same(zz.clone() * ff.clone(), zf.clone() * ff));
                assert!(same(zz.clone() / ff.clone(), zf.clone() / ff));
            }
        }
        #[cfg(feature = "rational")]
        for qq in &q {
            let qf = Float::with_val(check_prec, qq);
            for ff in &f {
                assert!(same(ff.clone() + qq, ff.clone() + &qf));
                assert!(same(ff.clone() - qq, ff.clone() - &qf));
                assert!(same(ff.clone() * qq, ff.clone() * &qf));
                assert!(same(ff.clone() / qq, ff.clone() / &qf));
                assert!(same(qq.clone() + ff.clone(), qf.clone() + ff));
                assert!(same(qq.clone() - ff.clone(), qf.clone() - ff));
                assert!(same(qq.clone() * ff.clone(), qf.clone() * ff));
                assert!(same(qq.clone() / ff.clone(), qf.clone() / ff));
            }
        }
        for uu in &u {
            let uf = Float::with_val(check_prec, *uu);
            for ff in &f {
                assert!(same(ff.clone() + *uu, ff.clone() + &uf));
                assert!(same(ff.clone() - *uu, ff.clone() - &uf));
                assert!(same(ff.clone() * *uu, ff.clone() * &uf));
                assert!(same(ff.clone() / *uu, ff.clone() / &uf));
                assert!(same(*uu + ff.clone(), uf.clone() + ff));
                assert!(same(*uu - ff.clone(), uf.clone() - ff));
                assert!(same(*uu * ff.clone(), uf.clone() * ff));
                assert!(same(*uu / ff.clone(), uf.clone() / ff));
            }
        }
        for ss in &s {
            let sf = Float::with_val(check_prec, *ss);
            for ff in &f {
                assert!(same(ff.clone() + *ss, ff.clone() + &sf));
                assert!(same(ff.clone() - *ss, ff.clone() - &sf));
                assert!(same(ff.clone() * *ss, ff.clone() * &sf));
                assert!(same(ff.clone() / *ss, ff.clone() / &sf));
                assert!(same(*ss + ff.clone(), sf.clone() + ff));
                assert!(same(*ss - ff.clone(), sf.clone() - ff));
                assert!(same(*ss * ff.clone(), sf.clone() * ff));
                assert!(same(*ss / ff.clone(), sf.clone() / ff));
            }
        }
        for oo in &double {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
        for oo in &single {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
    }

    #[test]
    fn check_from_str() {
        assert!(Float::from_str_radix("-@nan@", 2, 53).unwrap().is_nan());
        assert!(Float::from_str("-0", 53).unwrap().get_sign());
        assert!(!Float::from_str("+0", 53).unwrap().get_sign());
        assert!(Float::from_str("1e1000", 53).unwrap().is_finite());
        let huge_hex = "1@99999999999999999999999999999999";
        assert!(
            Float::from_str_radix(huge_hex, 16, 53)
                .unwrap()
                .is_infinite()
        );

        let bad_strings = [
            ("inf", 16),
            ("1e", 10),
            ("e10", 10),
            (".e10", 10),
            ("1e1.", 10),
            ("1e+-1", 10),
            ("1e-+1", 10),
            ("+-1", 10),
            ("-+1", 10),
            ("infinit", 10),
            ("1@1a", 16),
            ("9e0", 9),
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
            ("-abc.def@3", 16, -0xabcdef as f64),
            ("1e1023", 2, 2.0f64.powi(1023)),
        ];
        for &(s, radix, f) in good_strings.into_iter() {
            assert_eq!(Float::from_str_radix(s, radix, 53).unwrap(), f);
        }
    }

    #[test]
    fn check_formatting() {
        let mut f = Float::with_val(53, Special::Zero);
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "0.0");
        assert_eq!(format!("{:+?}", f), "+0.0");
        f.assign(Special::MinusZero);
        assert_eq!(format!("{}", f), "0.0");
        assert_eq!(format!("{:?}", f), "-0.0");
        assert_eq!(format!("{:+?}", f), "-0.0");
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
    }
}
