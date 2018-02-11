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

//! Multi-precision complex numbers with correct rounding.
//!
//! This module provides support for complex numbers of type
//! [`Complex`](../struct.Complex.html).

pub(crate) mod arith;
pub(crate) mod big;
mod cmp;
mod ord;
#[cfg(feature = "serde")]
mod serde;
mod small;
mod traits;

pub use complex::big::ParseComplexError;
#[allow(deprecated)]
pub use complex::big::ValidComplex;
pub use complex::ord::OrdComplex;
pub use complex::small::SmallComplex;

/// The `Prec` trait is used to specify the precision of the real and
/// imaginary parts of a [`Complex`](../struct.Complex.html) number.
///
/// This trait is implememented for `u32` and for `(u32, u32)`.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// let c1 = Complex::new(32);
/// assert_eq!(c1.prec(), (32, 32));
/// let c2 = Complex::new((32, 64));
/// assert_eq!(c2.prec(), (32, 64));
/// ```
pub trait Prec {
    /// Returns the precision for the real and imaginary parts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::Prec;
    /// assert_eq!(Prec::prec(24), (24, 24));
    /// assert_eq!(Prec::prec((24, 53)), (24, 53));
    /// ```
    fn prec(self) -> (u32, u32);
}

impl Prec for u32 {
    #[inline]
    fn prec(self) -> (u32, u32) {
        (self, self)
    }
}

impl Prec for (u32, u32) {
    #[inline]
    fn prec(self) -> (u32, u32) {
        self
    }
}

#[cfg(test)]
mod tests {
    use {Assign, Complex};
    use float::Special;
    use gmp_mpfr_sys::gmp;
    use std::f64;
    use std::mem;

    #[test]
    fn check_from_str() {
        let mut c = Complex::new(53);
        c.assign(Complex::parse("(+0 -0)", 10).unwrap());
        assert_eq!(c, (0, 0));
        assert!(c.real().is_sign_positive());
        assert!(c.imag().is_sign_negative());
        c.assign(Complex::parse("(5 6)", 10).unwrap());
        assert_eq!(c, (5, 6));
        c.assign(Complex::parse("(50 60)", 8).unwrap());
        assert_eq!(c, (0o50, 0o60));
        c.assign(Complex::parse("33", 16).unwrap());
        assert_eq!(c, (0x33, 0));

        let bad_strings = [
            ("(0 0 0)", None),
            ("(0) ", None),
            ("(, 0)", None),
            ("(0, )", None),
            ("(0,,0 )", None),
            (" ( 2)", None),
            ("+(1 1)", None),
            ("-(1. 1.)", None),
            ("(1 1@1a)", Some(16)),
            ("(8 )", Some(9)),
        ];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(
                Complex::parse(s, radix.unwrap_or(10)).is_err(),
                "{} parsed correctly",
                s
            );
        }
        let good_strings = [
            ("(inf -@inf@)", 10, f64::INFINITY, f64::NEG_INFINITY),
            ("(+0e99 1.)", 2, 0.0, 1.0),
            ("(+ 0 e 99, .1)", 2, 0.0, 0.5),
            ("-9.9e1", 10, -99.0, 0.0),
        ];
        for &(s, radix, r, i) in good_strings.into_iter() {
            match Complex::parse(s, radix) {
                Ok(ok) => {
                    let c = Complex::with_val(53, ok);
                    assert_eq!(*c.real(), r, "real mismatch for {}", s);
                    assert_eq!(*c.imag(), i, "imaginary mismatch for {}", s);
                }
                Err(e) => panic!("could not parse {} because {:?}", s, e),
            }
        }
    }

    #[test]
    fn check_formatting() {
        let mut c = Complex::new((53, 53));
        c.assign((Special::Zero, Special::NegZero));
        assert_eq!(format!("{}", c), "(0.0 -0.0)");
        assert_eq!(format!("{:?}", c), "(0.0 -0.0)");
        assert_eq!(format!("{:+}", c), "(+0.0 -0.0)");
        assert_eq!(format!("{:+}", *c.as_neg()), "(-0.0 +0.0)");
        c.assign((2.7, f64::NEG_INFINITY));
        assert_eq!(format!("{:.2}", c), "(2.7 -inf)");
        assert_eq!(format!("{:+.8}", c), "(+2.7000000 -inf)");
        assert_eq!(format!("{:.4e}", c), "(2.700 -inf)");
        assert_eq!(format!("{:.4E}", c), "(2.700 -inf)");
        assert_eq!(format!("{:16.2}", c), "      (2.7 -inf)");
        c.assign((-3.5, 11));
        assert_eq!(format!("{:.4b}", c), "(-1.110e1 1.011e3)");
        assert_eq!(format!("{:#.4b}", c), "(-0b1.110e1 0b1.011e3)");
        assert_eq!(format!("{:.4o}", c), "(-3.400 1.300e1)");
        assert_eq!(format!("{:#.4o}", c), "(-0o3.400 0o1.300e1)");
        c.assign((3.5, -11));
        assert_eq!(format!("{:.2x}", c), "(3.8 -b.0)");
        assert_eq!(format!("{:#.2x}", c), "(0x3.8 -0xb.0)");
        assert_eq!(format!("{:.2X}", c), "(3.8 -B.0)");
        assert_eq!(format!("{:#.2X}", c), "(0x3.8 -0xB.0)");
    }

    #[test]
    fn check_assumptions() {
        // we assume no nail bits when we use limbs
        assert_eq!(gmp::NAIL_BITS, 0);
        assert_eq!(gmp::NUMB_BITS, gmp::LIMB_BITS);
        assert_eq!(gmp::NUMB_BITS as usize, 8 * mem::size_of::<gmp::limb_t>());
    }
}
