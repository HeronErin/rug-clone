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

use crate::cast::{self, CheckedCast};
use crate::ext::xmpz;
use crate::integer::SmallInteger;
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
use std::os::raw::{c_long, c_ulong};

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
    PrimOps::add;
    Add { add }
    AddAssign { add_assign }
    AddFrom { add_from }
    i32, AddI32Incomplete;
    i64, AddI64Incomplete;
    u32, AddU32Incomplete;
    u64, AddU64Incomplete;
}
arith_prim_noncommut! {
    Integer;
    PrimOps::sub, PrimOps::sub_from;
    Sub { sub }
    SubAssign { sub_assign }
    SubFrom { sub_from }
    i32, SubI32Incomplete, SubFromI32Incomplete;
    i64, SubI64Incomplete, SubFromI64Incomplete;
    u32, SubU32Incomplete, SubFromU32Incomplete;
    u64, SubU64Incomplete, SubFromU64Incomplete;
}
arith_prim_commut! {
    Integer;
    PrimOps::mul;
    Mul { mul }
    MulAssign { mul_assign }
    MulFrom { mul_from }
    i32, MulI32Incomplete;
    i64, MulI64Incomplete;
    u32, MulU32Incomplete;
    u64, MulU64Incomplete;
}
arith_prim_noncommut! {
    Integer;
    PrimOps::div, PrimOps::div_from;
    Div { div }
    DivAssign { div_assign }
    DivFrom { div_from }
    i32, DivI32Incomplete, DivFromI32Incomplete;
    i64, DivI64Incomplete, DivFromI64Incomplete;
    u32, DivU32Incomplete, DivFromU32Incomplete;
    u64, DivU64Incomplete, DivFromU64Incomplete;
}
arith_prim_noncommut! {
    Integer;
    PrimOps::rem, PrimOps::rem_from;
    Rem { rem }
    RemAssign { rem_assign }
    RemFrom { rem_from }
    i32, RemI32Incomplete, RemFromI32Incomplete;
    i64, RemI64Incomplete, RemFromI64Incomplete;
    u32, RemU32Incomplete, RemFromU32Incomplete;
    u64, RemU64Incomplete, RemFromU64Incomplete;
}
arith_prim_commut! {
    Integer;
    PrimOps::and;
    BitAnd { bitand }
    BitAndAssign { bitand_assign }
    BitAndFrom { bitand_from }
    i32, BitAndI32Incomplete;
    i64, BitAndI64Incomplete;
    u32, BitAndU32Incomplete;
    u64, BitAndU64Incomplete;
}
arith_prim_commut! {
    Integer;
    PrimOps::ior;
    BitOr { bitor }
    BitOrAssign { bitor_assign }
    BitOrFrom { bitor_from }
    i32, BitOrI32Incomplete;
    i64, BitOrI64Incomplete;
    u32, BitOrU32Incomplete;
    u64, BitOrU64Incomplete;
}
arith_prim_commut! {
    Integer;
    PrimOps::xor;
    BitXor { bitxor }
    BitXorAssign { bitxor_assign }
    BitXorFrom { bitxor_from }
    i32, BitXorI32Incomplete;
    i64, BitXorI64Incomplete;
    u32, BitXorU32Incomplete;
    u64, BitXorU64Incomplete;
}

arith_prim! {
    Integer;
    xmpz::shl_i32;
    Shl { shl }
    ShlAssign { shl_assign }
    i32, ShlI32Incomplete;
}
arith_prim! {
    Integer;
    xmpz::shr_i32;
    Shr { shr }
    ShrAssign { shr_assign }
    i32, ShrI32Incomplete;
}
arith_prim! {
    Integer;
    xmpz::shl_u32;
    Shl { shl }
    ShlAssign { shl_assign }
    u32, ShlU32Incomplete;
}
arith_prim! {
    Integer;
    xmpz::shr_u32;
    Shr { shr }
    ShrAssign { shr_assign }
    u32, ShrU32Incomplete;
}
arith_prim! {
    Integer;
    xmpz::pow_u32;
    Pow { pow }
    PowAssign { pow_assign }
    u32, PowU32Incomplete;
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

trait PrimOps<Long>: AsLong {
    fn add(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn sub(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn sub_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn mul(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn div(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn div_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn rem(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn rem_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn and(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn ior(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn xor(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
}

trait AsLong: Copy {
    type Long;
}

macro_rules! as_long {
    ($Long:ty: $($Prim:ty)*) => { $(
        impl AsLong for $Prim {
            type Long = $Long;
        }
    )* }
}

as_long! { c_long: i8 i16 i32 i64 i128 isize }
as_long! { c_ulong: u8 u16 u32 u64 u128 usize }

macro_rules! forward {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        fn $fn(rop: &mut Integer, op1: Option<&Integer>, op2: Self) {
            if let Some(op2) = op2.checked_cast() {
                $deleg_long(rop, op1, op2);
            } else {
                let small: SmallInteger = op2.into();
                $deleg(rop, op1, Some(&*small));
            }
        }
    };
}
macro_rules! reverse {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        fn $fn(rop: &mut Integer, op1: Self, op2: Option<&Integer>) {
            if let Some(op1) = op1.checked_cast() {
                $deleg_long(rop, op1, op2);
            } else {
                let small: SmallInteger = op1.into();
                $deleg(rop, Some(&*small), op2);
            }
        }
    };
}

impl<T> PrimOps<c_long> for T
where
    T: AsLong<Long = c_long> + CheckedCast<c_long> + Into<SmallInteger>,
{
    forward! { fn add() -> xmpz::add_si, xmpz::add }
    forward! { fn sub() -> xmpz::sub_si, xmpz::sub }
    reverse! { fn sub_from() -> xmpz::si_sub, xmpz::sub }
    forward! { fn mul() -> xmpz::mul_si, xmpz::mul }
    forward! { fn div() -> xmpz::tdiv_q_si, xmpz::sub }
    reverse! { fn div_from() -> xmpz::si_tdiv_q, xmpz::sub }
    forward! { fn rem() -> xmpz::tdiv_r_si, xmpz::sub }
    reverse! { fn rem_from() -> xmpz::si_tdiv_r, xmpz::sub }
    forward! { fn and() -> xmpz::and_si, xmpz::and }
    forward! { fn ior() -> xmpz::ior_si, xmpz::ior }
    forward! { fn xor() -> xmpz::xor_si, xmpz::xor }
}

impl<T> PrimOps<c_ulong> for T
where
    T: AsLong<Long = c_ulong> + CheckedCast<c_ulong> + Into<SmallInteger>,
{
    forward! { fn add() -> xmpz::add_ui, xmpz::add }
    forward! { fn sub() -> xmpz::sub_ui, xmpz::sub }
    reverse! { fn sub_from() -> xmpz::ui_sub, xmpz::sub }
    forward! { fn mul() -> xmpz::mul_ui, xmpz::mul }
    forward! { fn div() -> xmpz::tdiv_q_ui, xmpz::sub }
    reverse! { fn div_from() -> xmpz::ui_tdiv_q, xmpz::sub }
    forward! { fn rem() -> xmpz::tdiv_r_ui, xmpz::sub }
    reverse! { fn rem_from() -> xmpz::ui_tdiv_r, xmpz::sub }
    forward! { fn and() -> xmpz::and_ui, xmpz::and }
    forward! { fn ior() -> xmpz::ior_ui, xmpz::ior }
    forward! { fn xor() -> xmpz::xor_ui, xmpz::xor }
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
        check_u_s!(I64, against);
        check_u_s!(U64, against);
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
