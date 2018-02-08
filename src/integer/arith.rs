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

use {Assign, Integer};
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use ops::{AddFrom, BitAndFrom, BitOrFrom, BitXorFrom, DivFrom, MulFrom,
          NegAssign, NotAssign, Pow, PowAssign, RemFrom, SubFrom};
use std::iter::{Product, Sum};
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign,
               BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg, Not,
               Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

arith_unary! { Integer; gmp::mpz_neg; Neg neg; NegAssign neg_assign; NegRef }
arith_binary! {
    Integer;
    gmp::mpz_add;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    AddRef
}
arith_binary! {
    Integer;
    gmp::mpz_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    SubRef
}
arith_binary! {
    Integer;
    gmp::mpz_mul;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    MulRef
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_q_check;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    DivRef
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_r_check;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    RemRef
}
arith_unary! { Integer; gmp::mpz_com; Not not; NotAssign not_assign; NotRef }
arith_binary! {
    Integer;
    gmp::mpz_and;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    BitAndRef
}
arith_binary! {
    Integer;
    gmp::mpz_ior;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    BitOrRef
}
arith_binary! {
    Integer;
    gmp::mpz_xor;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    BitXorRef
}

arith_prim_commut! {
    Integer;
    xgmp::mpz_add_si;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    i32;
    AddRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_sub_si, xgmp::mpz_si_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    i32;
    SubRefI32 SubFromRefI32
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_si;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    i32;
    MulRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_si_check, xgmp::mpz_si_tdiv_q_check;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    i32;
    DivRefI32 DivFromRefI32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_si_check, xgmp::mpz_si_tdiv_r_check;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    i32;
    RemRefI32 RemFromRefI32
}
arith_prim! {
    Integer; xgmp::mpz_lshift_si; Shl shl; ShlAssign shl_assign; i32; ShlRefI32
}
arith_prim! {
    Integer; xgmp::mpz_rshift_si; Shr shr; ShrAssign shr_assign; i32; ShrRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_si;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    i32;
    BitAndRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_si;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    i32;
    BitOrRefI32
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_si;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    i32;
    BitXorRefI32
}

arith_prim_commut! {
    Integer;
    gmp::mpz_add_ui;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    u32;
    AddRefU32
}
arith_prim_noncommut! {
    Integer;
    gmp::mpz_sub_ui, gmp::mpz_ui_sub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    u32;
    SubRefU32 SubFromRefU32
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_ui;
    Mul mul;
    MulAssign mul_assign;
    MulFrom mul_from;
    u32;
    MulRefU32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_ui_check, xgmp::mpz_ui_tdiv_q_check;
    Div div;
    DivAssign div_assign;
    DivFrom div_from;
    u32;
    DivRefU32 DivFromRefU32
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_ui_check, xgmp::mpz_ui_tdiv_r_check;
    Rem rem;
    RemAssign rem_assign;
    RemFrom rem_from;
    u32;
    RemRefU32 RemFromRefU32
}
arith_prim! {
    Integer; gmp::mpz_mul_2exp; Shl shl; ShlAssign shl_assign; u32; ShlRefU32
}
arith_prim! {
    Integer; gmp::mpz_fdiv_q_2exp; Shr shr; ShrAssign shr_assign; u32; ShrRefU32
}
arith_prim! {
    Integer; gmp::mpz_pow_ui; Pow pow; PowAssign pow_assign; u32; PowRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_ui;
    BitAnd bitand;
    BitAndAssign bitand_assign;
    BitAndFrom bitand_from;
    u32;
    BitAndRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_ui;
    BitOr bitor;
    BitOrAssign bitor_assign;
    BitOrFrom bitor_from;
    u32;
    BitOrRefU32
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_ui;
    BitXor bitxor;
    BitXorAssign bitxor_assign;
    BitXorFrom bitxor_from;
    u32;
    BitXorRefU32
}

mul_op_commut! {
    Integer;
    gmp::mpz_addmul;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    MulRef, inner;
    AddMulRef
}
mul_op_commut! {
    Integer;
    gmp::mpz_addmul_ui;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    MulRefU32, into;
    AddMulRefU32
}
mul_op_commut! {
    Integer;
    xgmp::mpz_addmul_si;
    Add add;
    AddAssign add_assign;
    AddFrom add_from;
    MulRefI32, into;
    AddMulRefI32
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul, xgmp::mpz_mulsub;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    MulRef, inner;
    SubMulRef SubMulRefFrom
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul_ui, xgmp::mpz_mulsub_ui;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    MulRefU32, into;
    SubMulRefU32 SubMulRefFromU32
}
mul_op_noncommut! {
    Integer;
    xgmp::mpz_submul_si, xgmp::mpz_mulsub_si;
    Sub sub;
    SubAssign sub_assign;
    SubFrom sub_from;
    MulRefI32, into;
    SubMulRefI32 SubMulRefFromI32
}

fold! { Integer, Sum sum, Integer::new(), Add::add }
fold! { Integer, Product product, Integer::from(1), Mul::mul }

#[cfg(test)]
mod tests {
    use Integer;
    use ops::Pow;
    use std::cmp::Ordering;

    #[test]
    fn check_arith_u_s() {
        use tests::{I32, I64, U32, U64};
        let large = &[(1, 100), (-11, 200), (33, 150)];
        let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
            .chain(U32.iter().map(|&x| Integer::from(x)))
            .chain(I32.iter().map(|&x| Integer::from(x)))
            .chain(U64.iter().map(|&x| Integer::from(x)))
            .chain(I64.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();

        for &op in U32 {
            let iop = Integer::from(op);
            for b in &against {
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
                assert_eq!(op + b.clone(), iop.clone() + b);
                assert_eq!(op - b.clone(), iop.clone() - b);
                assert_eq!(op * b.clone(), iop.clone() * b);
                if b.cmp0() != Ordering::Equal {
                    assert_eq!(op / b.clone(), iop.clone() / b);
                    assert_eq!(op % b.clone(), iop.clone() % b);
                }
                assert_eq!(op & b.clone(), iop.clone() & b);
                assert_eq!(op | b.clone(), iop.clone() | b);
                assert_eq!(op ^ b.clone(), iop.clone() ^ b);
            }
        }
        for &op in I32 {
            let iop = Integer::from(op);
            for b in &against {
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
                assert_eq!(op + b.clone(), iop.clone() + b);
                assert_eq!(op - b.clone(), iop.clone() - b);
                assert_eq!(op * b.clone(), iop.clone() * b);
                if b.cmp0() != Ordering::Equal {
                    assert_eq!(op / b.clone(), iop.clone() / b);
                    assert_eq!(op % b.clone(), iop.clone() % b);
                }
                assert_eq!(op & b.clone(), iop.clone() & b);
                assert_eq!(op | b.clone(), iop.clone() | b);
                assert_eq!(op ^ b.clone(), iop.clone() ^ b);
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
}
