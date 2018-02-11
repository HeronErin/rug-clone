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

//! Arbitrary-precision rational numbers.
//!
//! This module provides support for arbitrary-precision rational
//! numbers of type [`Rational`](../struct.Rational.html).

mod arith;
pub(crate) mod big;
mod cmp;
#[cfg(feature = "serde")]
mod serde;
mod small;
mod traits;

pub use rational::big::{MutNumerDenom, ParseRationalError};
#[allow(deprecated)]
pub use rational::big::ValidRational;
pub use rational::small::SmallRational;

#[cfg(test)]
mod tests {
    use {Integer, Rational};
    use gmp_mpfr_sys::gmp;
    use std::mem;

    #[test]
    fn check_fract_trunc() {
        let ndwf = [
            (23, 10, 2, 3),
            (-23, 10, -2, -3),
            (20, 10, 2, 0),
            (-20, 10, -2, 0),
            (3, 10, 0, 3),
            (-3, 10, 0, -3),
            (0, 10, 0, 0),
        ];
        for &(n, d, whole, fract_n) in ndwf.iter() {
            let r = Rational::from((n, d));

            let (fract, trunc) = r.clone().fract_trunc(Integer::new());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(trunc, whole);

            let (fract, trunc) =
                <(Rational, Integer)>::from(r.fract_trunc_ref());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(trunc, whole);

            let mut r = r;
            let mut trunc = Integer::new();
            r.fract_trunc_mut(&mut trunc);
            assert_eq!(r, (fract_n, d));
            assert_eq!(trunc, whole);
        }
    }

    #[test]
    fn check_fract_ceil() {
        let ndwf = [
            (23, 10, 3, -7),
            (-23, 10, -2, -3),
            (20, 10, 2, 0),
            (-20, 10, -2, 0),
            (3, 10, 1, -7),
            (-3, 10, 0, -3),
            (0, 10, 0, 0),
        ];
        for &(n, d, whole, fract_n) in ndwf.iter() {
            let r = Rational::from((n, d));

            let (fract, ceil) = r.clone().fract_ceil(Integer::new());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(ceil, whole);

            let (fract, ceil) = <(Rational, Integer)>::from(r.fract_ceil_ref());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(ceil, whole);

            let mut r = r;
            let mut ceil = Integer::new();
            r.fract_ceil_mut(&mut ceil);
            assert_eq!(r, (fract_n, d));
            assert_eq!(ceil, whole);
        }
    }

    #[test]
    fn check_fract_floor() {
        let ndwf = [
            (23, 10, 2, 3),
            (-23, 10, -3, 7),
            (20, 10, 2, 0),
            (-20, 10, -2, 0),
            (3, 10, 0, 3),
            (-3, 10, -1, 7),
            (0, 10, 0, 0),
        ];
        for &(n, d, whole, fract_n) in ndwf.iter() {
            let r = Rational::from((n, d));

            let (fract, floor) = r.clone().fract_floor(Integer::new());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(floor, whole);

            let (fract, floor) =
                <(Rational, Integer)>::from(r.fract_floor_ref());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(floor, whole);

            let mut r = r;
            let mut floor = Integer::new();
            r.fract_floor_mut(&mut floor);
            assert_eq!(r, (fract_n, d));
            assert_eq!(floor, whole);
        }
    }

    #[test]
    fn check_fract_round() {
        let ndwf = [
            (27, 10, 3, -3),
            (-27, 10, -3, 3),
            (25, 10, 3, -5),
            (-25, 10, -3, 5),
            (23, 10, 2, 3),
            (-23, 10, -2, -3),
            (20, 10, 2, 0),
            (-20, 10, -2, 0),
            (3, 10, 0, 3),
            (-3, 10, 0, -3),
            (0, 10, 0, 0),
        ];
        for &(n, d, whole, fract_n) in ndwf.iter() {
            let r = Rational::from((n, d));

            let (fract, round) = r.clone().fract_round(Integer::new());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(round, whole);

            let (fract, round) =
                <(Rational, Integer)>::from(r.fract_round_ref());
            assert_eq!(fract, (fract_n, d));
            assert_eq!(round, whole);

            let mut r = r;
            let mut round = Integer::new();
            r.fract_round_mut(&mut round);
            assert_eq!(r, (fract_n, d));
            assert_eq!(round, whole);
        }
    }

    #[test]
    fn check_from_str() {
        assert_eq!("-13/7".parse::<Rational>().unwrap(), (-13, 7));

        let bad_strings = [
            ("_1", None),
            ("+_1", None),
            ("-_1", None),
            ("1/_1", None),
            ("+-3", None),
            ("-+3", None),
            ("++3", None),
            ("--3", None),
            ("0+3", None),
            ("", None),
            ("1/-1", None),
            ("1/+3", None),
            ("1/0", None),
            ("/2", None),
            ("2/", None),
            ("2/2/", None),
            ("1/80", Some(8)),
            ("0xf", Some(16)),
            ("9", Some(9)),
            (":0", Some(36)),
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
                Rational::parse(s, radix.unwrap_or(10)).is_err(),
                "{} parsed correctly",
                s
            );
        }
        let good_strings = [
            ("0", 10, 0, 1),
            ("+0/fC", 16, 0, 1),
            (" + 1 _ / 2 _ ", 10, 1, 2),
            (" - 1 _ / 2 _ ", 10, -1, 2),
            ("-0/10", 2, 0, 1),
            ("-99/3", 10, -33, 1),
            ("+Ce/fF", 16, 0xce, 0xff),
            ("-77/2", 8, -0o77, 2),
            ("Z/z0", 36, 1, 36),
        ];
        for &(s, radix, n, d) in good_strings.into_iter() {
            match Rational::parse(s, radix) {
                Ok(ok) => {
                    let r = Rational::from(ok);
                    assert_eq!(*r.numer(), n, "numerator mismatch for {}", s);
                    assert_eq!(*r.denom(), d, "denominator mismatch for {}", s);
                }
                Err(_) => panic!("could not parse {}", s),
            }
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
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
    }
}
