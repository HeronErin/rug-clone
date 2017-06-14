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

//! TODO: document mod `complex`

mod big_complex;
mod small_complex;
mod xmpc;

pub use self::big_complex::{Complex, ParseComplexError, Prec, ValidComplex};
pub use self::small_complex::SmallComplex;

#[cfg(test)]
mod tests {
    use complex::Complex;
    use float::Special;
    use gmp_mpfr_sys::gmp;
    use ops::{Assign, Pow};
    use std::f64;
    use std::mem;

    #[test]
    fn check_ref_op() {
        let prec = (53, 53);
        let ri1 = (12.25, -1.375);
        let ri2 = (-1.375, 13);
        let lhs = Complex::from((ri1, prec));
        let rhs = Complex::from((ri2, prec));
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Complex::from((-&lhs, prec)), -lhs.clone());
        assert_eq!(Complex::from((&lhs + &rhs, prec)), lhs.clone() + &rhs);
        assert_eq!(Complex::from((&lhs - &rhs, prec)), lhs.clone() - &rhs);
        assert_eq!(Complex::from((&lhs * &rhs, prec)), lhs.clone() * &rhs);
        assert_eq!(Complex::from((&lhs / &rhs, prec)), lhs.clone() / &rhs);
        assert_eq!(
            Complex::from(((&lhs).pow(&rhs), prec)),
            lhs.clone().pow(&rhs)
        );

        assert_eq!(Complex::from((&lhs + pu, prec)), lhs.clone() + pu);
        assert_eq!(Complex::from((&lhs - pu, prec)), lhs.clone() - pu);
        assert_eq!(Complex::from((&lhs * pu, prec)), lhs.clone() * pu);
        assert_eq!(Complex::from((&lhs / pu, prec)), lhs.clone() / pu);
        assert_eq!(Complex::from((&lhs << pu, prec)), lhs.clone() << pu);
        assert_eq!(Complex::from((&lhs >> pu, prec)), lhs.clone() >> pu);
        assert_eq!(Complex::from(((&lhs).pow(pu), prec)), lhs.clone().pow(pu));

        assert_eq!(Complex::from((pu + &lhs, prec)), pu + lhs.clone());
        assert_eq!(Complex::from((pu - &lhs, prec)), pu - lhs.clone());
        assert_eq!(Complex::from((pu * &lhs, prec)), pu * lhs.clone());
        assert_eq!(Complex::from((pu / &lhs, prec)), pu / lhs.clone());

        assert_eq!(Complex::from((&lhs + pi, prec)), lhs.clone() + pi);
        assert_eq!(Complex::from((&lhs - pi, prec)), lhs.clone() - pi);
        assert_eq!(Complex::from((&lhs * pi, prec)), lhs.clone() * pi);
        assert_eq!(Complex::from((&lhs / pi, prec)), lhs.clone() / pi);
        assert_eq!(Complex::from((&lhs << pi, prec)), lhs.clone() << pi);
        assert_eq!(Complex::from((&lhs >> pi, prec)), lhs.clone() >> pi);
        assert_eq!(Complex::from(((&lhs).pow(pi), prec)), lhs.clone().pow(pi));

        assert_eq!(Complex::from((pi + &lhs, prec)), pi + lhs.clone());
        assert_eq!(Complex::from((pi - &lhs, prec)), pi - lhs.clone());
        assert_eq!(Complex::from((pi * &lhs, prec)), pi * lhs.clone());
        assert_eq!(Complex::from((pi / &lhs, prec)), pi / lhs.clone());

        assert_eq!(Complex::from(((&lhs).pow(ps), prec)), lhs.clone().pow(ps));
        assert_eq!(Complex::from(((&lhs).pow(pd), prec)), lhs.clone().pow(pd));
    }

    #[test]
    fn check_from_str() {
        let mut c = Complex::new((53, 53));
        c.assign_str("(+0 -0)").unwrap();
        assert_eq!(c, (0, 0));
        assert!(!c.real().get_sign());
        assert!(c.imag().get_sign());
        c.assign_str("(5 6)").unwrap();
        assert_eq!(c, (5, 6));
        c.assign_str_radix("(50 60)", 8).unwrap();
        assert_eq!(c, (0o50, 0o60));
        c.assign_str_radix("33", 16).unwrap();
        assert_eq!(c, (0x33, 0));

        let bad_strings = [
            ("(0,0)", None),
            ("(0 0 )", None),
            ("( 0 0)", None),
            ("( 0)", None),
            ("(0 )", None),
            (" ( 2)", None),
            ("+(1 1)", None),
            ("-(1. 1.)", None),
            ("(1 1@1a(", Some(16)),
            ("(8 9)", Some(9)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Complex::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings =
            [
                ("(inf -@inf@)", 10, f64::INFINITY, f64::NEG_INFINITY),
                ("(+0e99 1.)", 2, 0.0, 1.0),
                ("-9.9e1", 10, -99.0, 0.0),
            ];
        for &(s, radix, r, i) in good_strings.into_iter() {
            assert_eq!(
                Complex::from_str_radix(s, radix, (53, 53)).unwrap(),
                (r, i)
            );
        }
    }

    #[test]
    fn check_formatting() {
        let mut c = Complex::new((53, 53));
        c.assign((Special::Zero, Special::MinusZero));
        assert_eq!(format!("{}", c), "(0.0 0.0)");
        assert_eq!(format!("{:?}", c), "(0.0 -0.0)");
        assert_eq!(format!("{:+}", c), "(+0.0 -0.0)");
        c.assign((2.7, f64::NEG_INFINITY));
        assert_eq!(format!("{:.2}", c), "(2.7e0 -inf)");
        assert_eq!(format!("{:+.8}", c), "(+2.7000000e0 -inf)");
        assert_eq!(format!("{:.4e}", c), "(2.700e0 -inf)");
        assert_eq!(format!("{:.4E}", c), "(2.700E0 -inf)");
        assert_eq!(format!("{:16.2}", c), "    (2.7e0 -inf)");
        c.assign((3.5, 11));
        assert_eq!(format!("{:.4b}", c), "(1.110e1 1.011e3)");
        assert_eq!(format!("{:#.4b}", c), "(0b1.110e1 0b1.011e3)");
        assert_eq!(format!("{:.4o}", c), "(3.400e0 1.300e1)");
        assert_eq!(format!("{:#.4o}", c), "(0o3.400e0 0o1.300e1)");
        assert_eq!(format!("{:.2x}", c), "(3.8@0 b.0@0)");
        assert_eq!(format!("{:#.2x}", c), "(0x3.8@0 0xb.0@0)");
        assert_eq!(format!("{:.2X}", c), "(3.8@0 B.0@0)");
        assert_eq!(format!("{:#.2X}", c), "(0x3.8@0 0xB.0@0)");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
    }
}
