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

use ext::xmpz;
use gmp_mpfr_sys::gmp;
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
    xmpz::neg;
    Neg { neg }
    NegAssign { neg_assign }
    NegIncomplete
}
arith_binary! {
    Integer;
    xmpz::add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    AddIncomplete
}
arith_binary! {
    Integer;
    xmpz::sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    SubIncomplete
}
arith_binary! {
    Integer;
    xmpz::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    MulIncomplete
}
arith_binary! {
    Integer;
    xmpz::tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    DivIncomplete
}
arith_binary! {
    Integer;
    xmpz::tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    RemIncomplete
}
arith_unary! {
    Integer;
    xmpz::com;
    Not { not }
    NotAssign { not_assign }
    NotIncomplete
}
arith_binary! {
    Integer;
    xmpz::and;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    BitAndIncomplete
}
arith_binary! {
    Integer;
    xmpz::ior;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    BitOrIncomplete
}
arith_binary! {
    Integer;
    xmpz::xor;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    BitXorIncomplete
}

arith_prim_commut! {
    Integer;
    xmpz::add_i32;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    i32;
    AddI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::sub_i32, xmpz::i32_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    i32;
    SubI32Incomplete, SubFromI32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::mul_i32;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    i32;
    MulI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_q_i32, xmpz::i32_tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    i32;
    DivI32Incomplete, DivFromI32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_r_i32, xmpz::i32_tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    i32;
    RemI32Incomplete, RemFromI32Incomplete
}
arith_prim! {
    Integer;
    xmpz::lshift_i32;
    Shl { shl }
    ShlAssign { shl_assign }
    i32;
    ShlI32Incomplete
}
arith_prim! {
    Integer;
    xmpz::rshift_i32;
    Shr { shr }
    ShrAssign { shr_assign }
    i32;
    ShrI32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::and_i32;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    i32;
    BitAndI32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::ior_i32;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    i32;
    BitOrI32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::xor_i32;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    i32;
    BitXorI32Incomplete
}

arith_prim_commut! {
    Integer;
    xmpz::add_u32;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    u32;
    AddU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::sub_u32, xmpz::u32_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    u32;
    SubU32Incomplete, SubFromU32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::mul_u32;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    u32;
    MulU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_q_u32, xmpz::u32_tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    u32;
    DivU32Incomplete, DivFromU32Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_r_u32, xmpz::u32_tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    u32;
    RemU32Incomplete, RemFromU32Incomplete
}
arith_prim! {
    Integer;
    xmpz::mul_2exp;
    Shl { shl }
    ShlAssign { shl_assign }
    u32;
    ShlU32Incomplete
}
arith_prim! {
    Integer;
    xmpz::fdiv_q_2exp;
    Shr { shr }
    ShrAssign { shr_assign }
    u32;
    ShrU32Incomplete
}
arith_prim! {
    Integer;
    xmpz::pow_u32;
    Pow { pow }
    PowAssign { pow_assign }
    u32;
    PowU32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::and_u32;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    u32;
    BitAndU32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::ior_u32;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    u32;
    BitOrU32Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::xor_u32;
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
    MulIncomplete, as_raw;
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
    xmpz::mpz_addmul_si;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulI32Incomplete, into;
    AddMulI32Incomplete
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul, xmpz::mpz_mulsub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulIncomplete, as_raw;
    SubMulIncomplete, SubMulFromIncomplete
}
mul_op_noncommut! {
    Integer;
    gmp::mpz_submul_ui, xmpz::mpz_mulsub_ui;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulU32Incomplete, into;
    SubMulU32Incomplete, SubMulFromU32Incomplete
}
mul_op_noncommut! {
    Integer;
    xmpz::mpz_submul_si, xmpz::mpz_mulsub_si;
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
#[cfg_attr(feature = "cargo-clippy", allow(clippy::cyclomatic_complexity))]
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
