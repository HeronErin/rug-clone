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
// this program. If not, see <https://www.gnu.org/licenses/>.

use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use ops::{
    AddFrom, BitAndFrom, BitOrFrom, BitXorFrom, DivFrom, MulFrom, NegAssign,
    NotAssign, Pow, PowAssign, RemFrom, SubFrom,
};
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor,
    BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign,
    Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use {Assign, Integer};

arith_unary! {
    Integer;
    gmp::mpz_neg;
    Neg { neg }
    NegAssign { neg_assign }
    NegIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    AddIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    SubIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    MulIncomplete
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_q_check;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    DivIncomplete
}
arith_binary! {
    Integer;
    xgmp::mpz_tdiv_r_check;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    RemIncomplete
}
arith_unary! {
    Integer;
    gmp::mpz_com;
    Not { not }
    NotAssign { not_assign }
    NotIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_and;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    BitAndIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_ior;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    BitOrIncomplete
}
arith_binary! {
    Integer;
    gmp::mpz_xor;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    BitXorIncomplete
}

arith_prim_commut! {
    Integer;
    xgmp::mpz_add_si;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    i32;
    AddI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_sub_si, xgmp::mpz_si_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    i32;
    SubI32Incomplete, SubFromI32Incomplete
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_si;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    i32;
    MulI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_si_check, xgmp::mpz_si_tdiv_q_check;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    i32;
    DivI32Incomplete, DivFromI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_si_check, xgmp::mpz_si_tdiv_r_check;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    i32;
    RemI32Incomplete, RemFromI32Incomplete
}
arith_prim! {
    Integer;
    xgmp::mpz_lshift_si;
    Shl { shl }
    ShlAssign { shl_assign }
    i32;
    ShlI32Incomplete
}
arith_prim! {
    Integer;
    xgmp::mpz_rshift_si;
    Shr { shr }
    ShrAssign { shr_assign }
    i32;
    ShrI32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_si;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    i32;
    BitAndI32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_si;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    i32;
    BitOrI32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_si;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    i32;
    BitXorI32Incomplete
}

arith_prim_commut! {
    Integer;
    gmp::mpz_add_ui;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    u32;
    AddU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    gmp::mpz_sub_ui, gmp::mpz_ui_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    u32;
    SubU32Incomplete, SubFromU32Incomplete
}
arith_prim_commut! {
    Integer;
    gmp::mpz_mul_ui;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    u32;
    MulU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_q_ui_check, xgmp::mpz_ui_tdiv_q_check;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    u32;
    DivU32Incomplete, DivFromU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xgmp::mpz_tdiv_r_ui_check, xgmp::mpz_ui_tdiv_r_check;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    u32;
    RemU32Incomplete, RemFromU32Incomplete
}
arith_prim! {
    Integer;
    gmp::mpz_mul_2exp;
    Shl { shl }
    ShlAssign { shl_assign }
    u32;
    ShlU32Incomplete
}
arith_prim! {
    Integer;
    gmp::mpz_fdiv_q_2exp;
    Shr { shr }
    ShrAssign { shr_assign }
    u32;
    ShrU32Incomplete
}
arith_prim! {
    Integer;
    gmp::mpz_pow_ui;
    Pow { pow }
    PowAssign { pow_assign }
    u32;
    PowU32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitand_ui;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    u32;
    BitAndU32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitor_ui;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    u32;
    BitOrU32Incomplete
}
arith_prim_commut! {
    Integer;
    xgmp::bitxor_ui;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    u32;
    BitXorU32Incomplete
}

mul_op_commut! {
    Integer;
    gmp::mpz_addmul;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulIncomplete, inner;
    AddMulIncomplete
}
mul_op_commut! {
    Integer;
    gmp::mpz_addmul_ui;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulU32Incomplete, into;
    AddMulU32Incomplete
}
mul_op_commut! {
    Integer;
    xgmp::mpz_addmul_si;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulI32Incomplete, into;
    AddMulI32Incomplete
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul, xgmp::mpz_mulsub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulIncomplete, inner;
    SubMulIncomplete, SubMulFromIncomplete
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul_ui, xgmp::mpz_mulsub_ui;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulU32Incomplete, into;
    SubMulU32Incomplete, SubMulFromU32Incomplete
}
mul_op_noncommut! {
    Integer;
    xgmp::mpz_submul_si, xgmp::mpz_mulsub_si;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulI32Incomplete, into;
    SubMulI32Incomplete, SubMulFromI32Incomplete
}

impl<T> Sum<T> for Integer
where
    Integer: AddAssign<T>,
{
    fn sum<I>(iter: I) -> Integer
    where
        I: Iterator<Item = T>,
    {
        let mut ret = Integer::new();
        for i in iter {
            ret.add_assign(i);
        }
        ret
    }
}

impl<T> Product<T> for Integer
where
    Integer: MulAssign<T>,
{
    fn product<I>(iter: I) -> Integer
    where
        I: Iterator<Item = T>,
    {
        let mut ret = Integer::from(1);
        for i in iter {
            ret.mul_assign(i);
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use ops::{AddFrom, Pow, SubFrom};
    use std::cmp::Ordering;
    use std::ops::{AddAssign, SubAssign};
    use Integer;

    #[test]
    fn check_arith_u_s() {
        #[cfg(int_128)]
        use tests::{I128, U128};
        use tests::{I32, I64, U32, U64};
        let large = [(1, 100), (-11, 200), (33, 150)];
        let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
            .chain(U32.iter().map(|&x| Integer::from(x)))
            .chain(I32.iter().map(|&x| Integer::from(x)))
            .chain(U64.iter().map(|&x| Integer::from(x)))
            .chain(I64.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();
        #[cfg(int_128)]
        let mut against = against;
        #[cfg(int_128)]
        {
            against.extend(U128.iter().map(|&x| Integer::from(x)));
            against.extend(I128.iter().map(|&x| Integer::from(x)));
        }

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

    macro_rules! test_ref_op {
        ($first:expr, $second:expr) => {
            assert_eq!(
                Integer::from($first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Integer::from(0x00ff);
        let rhs = Integer::from(0x0f0f);
        let pu = 30_u32;
        let pi = -15_i32;
        test_ref_op!(-&lhs, -lhs.clone());
        test_ref_op!(&lhs + &rhs, lhs.clone() + &rhs);
        test_ref_op!(&lhs - &rhs, lhs.clone() - &rhs);
        test_ref_op!(&lhs * &rhs, lhs.clone() * &rhs);
        test_ref_op!(&lhs / &rhs, lhs.clone() / &rhs);
        test_ref_op!(&lhs % &rhs, lhs.clone() % &rhs);
        test_ref_op!(!&lhs, !lhs.clone());
        test_ref_op!(&lhs & &rhs, lhs.clone() & &rhs);
        test_ref_op!(&lhs | &rhs, lhs.clone() | &rhs);
        test_ref_op!(&lhs ^ &rhs, lhs.clone() ^ &rhs);

        test_ref_op!(&lhs + pu, lhs.clone() + pu);
        test_ref_op!(&lhs - pu, lhs.clone() - pu);
        test_ref_op!(&lhs * pu, lhs.clone() * pu);
        test_ref_op!(&lhs / pu, lhs.clone() / pu);
        test_ref_op!(&lhs % pu, lhs.clone() % pu);
        test_ref_op!(&lhs & pu, lhs.clone() & pu);
        test_ref_op!(&lhs | pu, lhs.clone() | pu);
        test_ref_op!(&lhs ^ pu, lhs.clone() ^ pu);
        test_ref_op!(&lhs << pu, lhs.clone() << pu);
        test_ref_op!(&lhs >> pu, lhs.clone() >> pu);
        test_ref_op!((&lhs).pow(pu), lhs.clone().pow(pu));

        test_ref_op!(&lhs + pi, lhs.clone() + pi);
        test_ref_op!(&lhs - pi, lhs.clone() - pi);
        test_ref_op!(&lhs * pi, lhs.clone() * pi);
        test_ref_op!(&lhs / pi, lhs.clone() / pi);
        test_ref_op!(&lhs % pi, lhs.clone() % pi);
        test_ref_op!(&lhs & pi, lhs.clone() & pi);
        test_ref_op!(&lhs | pi, lhs.clone() | pi);
        test_ref_op!(&lhs ^ pi, lhs.clone() ^ pi);
        test_ref_op!(&lhs << pi, lhs.clone() << pi);
        test_ref_op!(&lhs >> pi, lhs.clone() >> pi);

        test_ref_op!(pu + &lhs, pu + lhs.clone());
        test_ref_op!(pu - &lhs, pu - lhs.clone());
        test_ref_op!(pu * &lhs, pu * lhs.clone());
        test_ref_op!(pu / &lhs, pu / lhs.clone());
        test_ref_op!(pu % &lhs, pu % lhs.clone());
        test_ref_op!(pu & &lhs, pu & lhs.clone());
        test_ref_op!(pu | &lhs, pu | lhs.clone());
        test_ref_op!(pu ^ &lhs, pu ^ lhs.clone());

        test_ref_op!(pi + &lhs, pi + lhs.clone());
        test_ref_op!(pi - &lhs, pi - lhs.clone());
        test_ref_op!(pi * &lhs, pi * lhs.clone());
        test_ref_op!(pi / &lhs, pi / lhs.clone());
        test_ref_op!(pi % &lhs, pi % lhs.clone());
        test_ref_op!(pi & &lhs, pi & lhs.clone());
        test_ref_op!(pi | &lhs, pi | lhs.clone());
        test_ref_op!(pi ^ &lhs, pi ^ lhs.clone());
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

    fn check_single_addmul<F, T>(i: &mut Integer, j: &mut i32, f: F, u: i32)
    where
        F: Fn() -> T,
        Integer: AddAssign<T> + AddFrom<T>,
    {
        *i += f();
        *j += u;
        assert_eq!(i, j);
        i.add_from(f());
        j.add_from(u);
        assert_eq!(i, j);
    }

    fn check_single_submul<F, T>(i: &mut Integer, j: &mut i32, f: F, u: i32)
    where
        F: Fn() -> T,
        Integer: SubAssign<T> + SubFrom<T>,
    {
        *i -= f();
        *j -= u;
        assert_eq!(i, j);
        i.sub_from(f());
        j.sub_from(u);
        assert_eq!(i, j);
    }

    #[test]
    fn check_addmul() {
        let mut i = Integer::from(10);
        let mut j = 10i32;
        let two = Integer::from(2);

        check_single_addmul(&mut i, &mut j, || &two * &two, 2 * 2);
        check_single_addmul(&mut i, &mut j, || &two * 12u32, 2 * 12);
        check_single_addmul(&mut i, &mut j, || 13u32 * &two, 13 * 2);
        check_single_addmul(&mut i, &mut j, || &two * 14i32, 2 * 14);
        check_single_addmul(&mut i, &mut j, || 15i32 * &two, 15 * 2);
        check_single_addmul(&mut i, &mut j, || &two * -16i32, 2 * -16);
        check_single_addmul(&mut i, &mut j, || -17i32 * &two, -17 * 2);
    }

    #[test]
    fn check_submul() {
        let mut i = Integer::from(10);
        let mut j = 10i32;
        let two = Integer::from(2);

        check_single_submul(&mut i, &mut j, || &two * &two, 2 * 2);
        check_single_submul(&mut i, &mut j, || &two * 12u32, 2 * 12);
        check_single_submul(&mut i, &mut j, || 13u32 * &two, 13 * 2);
        check_single_submul(&mut i, &mut j, || &two * 14i32, 2 * 14);
        check_single_submul(&mut i, &mut j, || 15i32 * &two, 15 * 2);
        check_single_submul(&mut i, &mut j, || &two * -16i32, 2 * -16);
        check_single_submul(&mut i, &mut j, || -17i32 * &two, -17 * 2);
    }
}
