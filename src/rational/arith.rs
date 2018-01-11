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

use {Assign, Rational};
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use ops::{AddFrom, DivFrom, MulFrom, NegAssign, Pow, PowAssign, SubFrom};
use std::i32;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};

arith_unary! { Rational; gmp::mpq_neg; Neg neg; NegAssign neg_assign; NegRef }
arith_binary! {
    Rational;
    gmp::mpq_add;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    AddRef
}
arith_binary! {
    Rational;
    gmp::mpq_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    SubRef
}
arith_binary! {
    Rational;
    gmp::mpq_mul;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    MulRef
}
arith_binary! {
    Rational;
    gmp::mpq_div;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    DivRef
}

arith_prim! {
    Rational;
    xgmp::mpq_mul_2exp_si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlRefI32
}
arith_prim! {
    Rational;
    xgmp::mpq_div_2exp_si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrRefI32
}
arith_prim! {
    Rational; xgmp::mpq_pow_si; Pow pow; PowAssign pow_assign; i32; PowRefI32
}

arith_prim! {
    Rational; gmp::mpq_mul_2exp; Shl shl; ShlAssign shl_assign; u32; ShlRefU32
}
arith_prim! {
    Rational; gmp::mpq_div_2exp; Shr shr; ShrAssign shr_assign; u32; ShrRefU32
}
arith_prim! {
    Rational; xgmp::mpq_pow_ui; Pow pow; PowAssign pow_assign; u32; PowRefU32
}

sum_prod! { Rational, Rational::new(), Rational::from(1) }

#[cfg(test)]
mod tests {
    use Rational;
    use ops::Pow;

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
}
