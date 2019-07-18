// Copyright © 2016–2019 University of Malta

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
// this program. If not, see <https://www.gnu.org/licenses/>.

use crate::ext::xmpq;
use crate::ops::{AddFrom, DivFrom, MulFrom, NegAssign, Pow, PowAssign, SubFrom};
use crate::{Assign, Rational};
use std::i32;
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
    SubAssign,
};

// Specialize From implementation so that allocation is done with the
// right capacity, as Rational::from(&Rational) allocates properly.
arith_unary! {
    Rational;
    xmpq::neg;
    Neg { neg }
    NegAssign { neg_assign }
    NegIncomplete;
    fn from_incomplete(src) {
        let mut dst = Rational::from(src.op);
        dst.neg_assign();
        dst
    }
}
arith_binary! {
    Rational;
    xmpq::add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    AddIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Rational;
    xmpq::sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    SubIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Rational;
    xmpq::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    MulIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Rational;
    xmpq::div;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    DivIncomplete;
    rhs_has_more_alloc
}

arith_prim! {
    Rational;
    xmpq::lshift_i32;
    Shl { shl }
    ShlAssign { shl_assign }
    i32, ShlI32Incomplete;
}
arith_prim! {
    Rational;
    xmpq::rshift_i32;
    Shr { shr }
    ShrAssign { shr_assign }
    i32, ShrI32Incomplete;
}
arith_prim! {
    Rational;
    xmpq::pow_i32;
    Pow { pow }
    PowAssign { pow_assign }
    i32, PowI32Incomplete;
}

arith_prim! {
    Rational;
    xmpq::mul_2exp;
    Shl { shl }
    ShlAssign { shl_assign }
    u32, ShlU32Incomplete;
}
arith_prim! {
    Rational;
    xmpq::div_2exp;
    Shr { shr }
    ShrAssign { shr_assign }
    u32, ShrU32Incomplete;
}
arith_prim! {
    Rational;
    xmpq::pow_u32;
    Pow { pow }
    PowAssign { pow_assign }
    u32, PowU32Incomplete;
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

#[inline]
fn rhs_has_more_alloc(lhs: &Rational, rhs: &Rational) -> bool {
    // This can overflow:
    //     lhs.num.alloc + lhs.den.alloc < rhs.num.alloc + rhs.den.alloc
    // Since all alloc are non-negative signed integers (c_int), this
    // cannot overflow:
    //     lhs.num.alloc - rhs.den.alloc < rhs.num.alloc - lhs.den.alloc
    lhs.numer().inner().alloc - rhs.denom().inner().alloc
        < rhs.numer().inner().alloc - lhs.denom().inner().alloc
}

#[cfg(test)]
mod tests {
    use crate::ops::Pow;
    use crate::Rational;

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
