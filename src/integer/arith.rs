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

use crate::cast;
use crate::ext::xmpz;
use crate::misc::NegAbs;
use crate::ops::{
    AddFrom, BitAndFrom, BitOrFrom, BitXorFrom, DivFrom, MulFrom, NegAssign, NotAssign, Pow,
    PowAssign, RemFrom, SubFrom,
};
use crate::{Assign, Integer};
use gmp_mpfr_sys::gmp;
use std::cmp;
use std::iter::{Product, Sum};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

// Specialize From implementation so that allocation is done with the
// right capacity, as Integer::from(&Integer) allocates properly.
arith_unary! {
    Integer;
    xmpz::neg;
    Neg { neg }
    NegAssign { neg_assign }
    NegIncomplete;
    // Specialize so that allocation is done with the right capacity,
    // as Integer::from(&Integer) allocates properly.
    fn from_incomplete(src) {
        let mut dst = Integer::from(src.op);
        dst.neg_assign();
        dst
    }
}
arith_binary! {
    Integer;
    xmpz::add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    AddIncomplete;
    rhs_has_more_alloc;
    // Specialize so that allocation is done with the right capacity.
    fn from_incomplete(src) {
        let mut dst = alloc_for_add(&src.lhs, &src.rhs);
        dst.assign(src);
        dst
    }
}
arith_binary! {
    Integer;
    xmpz::sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    SubIncomplete;
    rhs_has_more_alloc;
    // Specialize so that allocation is done with the right capacity.
    fn from_incomplete(src) {
        let mut dst = alloc_for_add(&src.lhs, &src.rhs);
        dst.assign(src);
        dst
    }
}
arith_binary! {
    Integer;
    xmpz::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    MulIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Integer;
    xmpz::tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    DivIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Integer;
    xmpz::tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    RemIncomplete;
    rhs_has_more_alloc
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
    BitAndIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Integer;
    xmpz::ior;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    BitOrIncomplete;
    rhs_has_more_alloc
}
arith_binary! {
    Integer;
    xmpz::xor;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    BitXorIncomplete;
    rhs_has_more_alloc
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

arith_prim_commut! {
    Integer;
    xmpz::add_i64;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    i64;
    AddI64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::sub_i64, xmpz::i64_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    i64;
    SubI64Incomplete, SubFromI64Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::mul_i64;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    i64;
    MulI64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_q_i64, xmpz::i64_tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    i64;
    DivI64Incomplete, DivFromI64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_r_i64, xmpz::i64_tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    i64;
    RemI64Incomplete, RemFromI64Incomplete
}

arith_prim_commut! {
    Integer;
    xmpz::add_u64;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    u64;
    AddU64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::sub_u64, xmpz::u64_sub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    u64;
    SubU64Incomplete, SubFromU64Incomplete
}
arith_prim_commut! {
    Integer;
    xmpz::mul_u64;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    u64;
    MulU64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_q_u64, xmpz::u64_tdiv_q;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    u64;
    DivU64Incomplete, DivFromU64Incomplete
}
arith_prim_noncommut! {
    Integer;
    xmpz::tdiv_r_u64, xmpz::u64_tdiv_r;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    u64;
    RemU64Incomplete, RemFromU64Incomplete
}

mul_op_commut! {
    Integer;
    xmpz::addmul;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulIncomplete;
    AddMulIncomplete
}
mul_op_commut! {
    Integer;
    xmpz::addmul_u32;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulU32Incomplete;
    AddMulU32Incomplete
}
mul_op_commut! {
    Integer;
    xmpz::addmul_i32;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    MulI32Incomplete;
    AddMulI32Incomplete
}
mul_op_noncommut! {
    Integer;
    xmpz::submul, xmpz::mulsub;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulIncomplete;
    SubMulIncomplete, SubMulFromIncomplete
}
mul_op_noncommut! {
    Integer;
    xmpz::submul_u32, xmpz::mulsub_u32;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulU32Incomplete;
    SubMulU32Incomplete, SubMulFromU32Incomplete
}
mul_op_noncommut! {
    Integer;
    xmpz::submul_i32, xmpz::mulsub_i32;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    MulI32Incomplete;
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

#[inline]
fn alloc_for_add(lhs: &Integer, rhs: &Integer) -> Integer {
    let lhs_size = lhs.inner().size.neg_abs().1;
    let rhs_size = rhs.inner().size.neg_abs().1;
    let size = cmp::max(lhs_size, rhs_size);
    let size = cast::cast::<_, usize>(size);
    // size must be < max, not just ≤ max, because we need to add 1 to it
    assert!(
        size < usize::max_value() / (gmp::LIMB_BITS as usize),
        "overflow"
    );
    Integer::with_capacity((size + 1) * (gmp::LIMB_BITS as usize))
}

#[inline]
fn rhs_has_more_alloc(lhs: &Integer, rhs: &Integer) -> bool {
    lhs.inner().alloc < rhs.inner().alloc
}

#[cfg(test)]
#[allow(clippy::cognitive_complexity)]
mod tests {
    use crate::ops::{AddFrom, Pow, SubFrom};
    use crate::Integer;
    use std::cmp::Ordering;
    use std::ops::{AddAssign, SubAssign};

    macro_rules! test_op {
        ($lhs:ident $op:tt $rhs:ident) => {
            let ans = $lhs.clone() $op $rhs.clone();
            assert_eq!(ans, $lhs.clone() $op $rhs);
            assert_eq!(ans, $lhs $op $rhs.clone());
            assert_eq!(ans, Integer::from($lhs $op $rhs));
        };
    }

    #[test]
    fn check_arith() {
        use crate::tests::{I128, I32, I64, U128, U32, U64};
        let large = [(1, 100), (-11, 200), (33, 150)];
        let all = (large.iter().map(|&(n, s)| Integer::from(n) << s))
            .chain(U32.iter().map(|&x| Integer::from(x)))
            .chain(I32.iter().map(|&x| Integer::from(x)))
            .chain(U64.iter().map(|&x| Integer::from(x)))
            .chain(I64.iter().map(|&x| Integer::from(x)))
            .chain(U128.iter().map(|&x| Integer::from(x)))
            .chain(I128.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();

        for l in &all {
            for r in &all {
                test_op!(l + r);
                test_op!(l - r);
                test_op!(l * r);
                if r.cmp0() != Ordering::Equal {
                    test_op!(l / r);
                }
                test_op!(l & r);
                test_op!(l | r);
                test_op!(l ^ r);
            }
        }
    }

    macro_rules! check_u_s {
        ($list:expr, $against:expr) => {
            for &op in $list {
                let iop = Integer::from(op);
                for b in &$against {
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
        };
        ($list:expr, $against:expr, reduced) => {
            for &op in $list {
                let iop = Integer::from(op);
                for b in &$against {
                    assert_eq!(b.clone() + op, b.clone() + &iop);
                    assert_eq!(b.clone() - op, b.clone() - &iop);
                    assert_eq!(b.clone() * op, b.clone() * &iop);
                    if op != 0 {
                        assert_eq!(b.clone() / op, b.clone() / &iop);
                        assert_eq!(b.clone() % op, b.clone() % &iop);
                    }
                    // assert_eq!(b.clone() & op, b.clone() & &iop);
                    // assert_eq!(b.clone() | op, b.clone() | &iop);
                    // assert_eq!(b.clone() ^ op, b.clone() ^ &iop);
                    assert_eq!(op + b.clone(), iop.clone() + b);
                    assert_eq!(op - b.clone(), iop.clone() - b);
                    assert_eq!(op * b.clone(), iop.clone() * b);
                    if b.cmp0() != Ordering::Equal {
                        assert_eq!(op / b.clone(), iop.clone() / b);
                        assert_eq!(op % b.clone(), iop.clone() % b);
                    }
                    // assert_eq!(op & b.clone(), iop.clone() & b);
                    // assert_eq!(op | b.clone(), iop.clone() | b);
                    // assert_eq!(op ^ b.clone(), iop.clone() ^ b);
                }
            }
        };
    }

    #[test]
    fn check_arith_u_s() {
        use crate::tests::{I128, I32, I64, U128, U32, U64};
        let large = [(1, 100), (-11, 200), (33, 150)];
        let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
            .chain(U32.iter().map(|&x| Integer::from(x)))
            .chain(I32.iter().map(|&x| Integer::from(x)))
            .chain(U64.iter().map(|&x| Integer::from(x)))
            .chain(I64.iter().map(|&x| Integer::from(x)))
            .chain(U128.iter().map(|&x| Integer::from(x)))
            .chain(I128.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();

        check_u_s!(I32, against);
        check_u_s!(U32, against);
        check_u_s!(I64, against, reduced);
        check_u_s!(U64, against, reduced);
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
