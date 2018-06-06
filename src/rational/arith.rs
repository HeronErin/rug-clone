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

use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use ops::{AddFrom, DivFrom, MulFrom, NegAssign, Pow, PowAssign, SubFrom};
use std::i32;
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr,
    ShrAssign, Sub, SubAssign,
};
use {Assign, Rational};

arith_unary! {
    Rational;
    gmp::mpq_neg;
    Neg { neg }
    NegAssign { neg_assign }
    NegIncomplete
}
arith_binary! {
    Rational;
    gmp::mpq_add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    AddIncomplete
}
arith_binary! {
    Rational;
    gmp::mpq_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    SubIncomplete
}
arith_binary! {
    Rational;
    gmp::mpq_mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    MulIncomplete
}
arith_binary! {
    Rational;
    gmp::mpq_div;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    DivIncomplete
}

arith_prim! {
    Rational;
    xgmp::mpq_mul_2exp_si;
    Shl { shl }
    ShlAssign { shl_assign }
    i32;
    ShlI32Incomplete
}
arith_prim! {
    Rational;
    xgmp::mpq_div_2exp_si;
    Shr { shr }
    ShrAssign { shr_assign }
    i32;
    ShrI32Incomplete
}
arith_prim! {
    Rational;
    xgmp::mpq_pow_si;
    Pow { pow }
    PowAssign { pow_assign }
    i32;
    PowI32Incomplete
}

arith_prim! {
    Rational;
    gmp::mpq_mul_2exp;
    Shl { shl }
    ShlAssign { shl_assign }
    u32;
    ShlU32Incomplete
}
arith_prim! {
    Rational;
    gmp::mpq_div_2exp;
    Shr { shr }
    ShrAssign { shr_assign }
    u32;
    ShrU32Incomplete
}
arith_prim! {
    Rational;
    xgmp::mpq_pow_ui;
    Pow { pow }
    PowAssign { pow_assign }
    u32;
    PowU32Incomplete
}

impl<T> Sum<T> for Rational
where
    Rational: AddAssign<T>,
{
    fn sum<I>(iter: I) -> Rational
    where
        I: Iterator<Item = T>,
    {
        let mut ret = Rational::new();
        for i in iter {
            ret.add_assign(i);
        }
        ret
    }
}

impl<T> Product<T> for Rational
where
    Rational: MulAssign<T>,
{
    fn product<I>(iter: I) -> Rational
    where
        I: Iterator<Item = T>,
    {
        let mut ret = Rational::from(1);
        for i in iter {
            ret.mul_assign(i);
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use ops::Pow;
    use Rational;

    macro_rules! test_ref_op {
        ($first:expr, $second:expr) => {
            assert_eq!(
                Rational::from($first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Rational::from((-13, 27));
        let rhs = Rational::from((15, 101));
        let pu = 30_u32;
        let pi = -15_i32;
        test_ref_op!(-&lhs, -lhs.clone());
        test_ref_op!(&lhs + &rhs, lhs.clone() + &rhs);
        test_ref_op!(&lhs - &rhs, lhs.clone() - &rhs);
        test_ref_op!(&lhs * &rhs, lhs.clone() * &rhs);
        test_ref_op!(&lhs / &rhs, lhs.clone() / &rhs);

        test_ref_op!(&lhs << pu, lhs.clone() << pu);
        test_ref_op!(&lhs >> pu, lhs.clone() >> pu);
        test_ref_op!((&lhs).pow(pu), lhs.clone().pow(pu));

        test_ref_op!(&lhs << pi, lhs.clone() << pi);
        test_ref_op!(&lhs >> pi, lhs.clone() >> pi);
        test_ref_op!((&lhs).pow(pi), lhs.clone().pow(pi));
    }
}
