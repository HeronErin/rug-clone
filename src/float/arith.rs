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

use Float;
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use ext::mpfr as xmpfr;
use float::{Round, Special};
use float::big::{raw_round, ordering1};
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use inner::{Inner, InnerMut};
use ops::{AddAssignRound, AddFrom, AddFromRound, AssignRound, DivAssignRound,
          DivFrom, DivFromRound, MulAssignRound, MulFrom, MulFromRound,
          NegAssign, Pow, PowAssign, PowAssignRound, PowFrom, PowFromRound,
          SubAssignRound, SubFrom, SubFromRound};
use std::{i32, u32};
use std::cmp::Ordering;
use std::iter::{Product, Sum};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::c_int;

impl Neg for Float {
    type Output = Float;
    #[inline]
    fn neg(mut self) -> Float {
        self.neg_assign();
        self
    }
}

impl NegAssign for Float {
    #[inline]
    fn neg_assign(&mut self) {
        unsafe {
            self.inner_mut().sign.neg_assign();
            if self.is_nan() {
                mpfr::set_nanflag();
            }
        }
    }
}

impl<'a> Neg for &'a Float {
    type Output = NegRef<'a>;
    #[inline]
    fn neg(self) -> NegRef<'a> {
        NegRef { val: self }
    }
}

#[derive(Clone, Copy)]
pub struct NegRef<'a> {
    val: &'a Float,
}

impl<'a> AssignRound<NegRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NegRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::neg(self.inner_mut(), src.val.inner(), raw_round(round))
        };
        ordering1(ret)
    }
}

macro_rules! arith_binary_self_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Ref:ident
    } => {
        arith_binary_self_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Ref
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_forward_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident $OwnedRef:ident
    } => {
        arith_forward_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $OwnedRef
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_commut_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $OwnedRef:ident
    } => {
        arith_commut_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $OwnedRef
        }
    }
}

#[cfg(feature = "integer")]
macro_rules! arith_noncommut_float {
    {
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $FromRef:ident $OwnedRef:ident $FromOwnedRef:ident
    } => {
        arith_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $FromRef $OwnedRef $FromOwnedRef
        }
    }
}

arith_binary_self_float! {
    mpfr::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddRef
}
arith_binary_self_float! {
    mpfr::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubRef
}
arith_binary_self_float! {
    mpfr::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulRef
}
arith_binary_self_float! {
    mpfr::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivRef
}
arith_binary_self_float! {
    mpfr::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowRef
}

#[cfg(feature = "integer")]
arith_commut_float! {
    mpfr::add_z;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Integer;
    AddIntegerRef AddOwnedIntegerRef
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::sub_z, mpfr::z_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Integer;
    SubIntegerRef SubFromIntegerRef SubOwnedIntegerRef SubFromOwnedIntegerRef
}
#[cfg(feature = "integer")]
arith_commut_float! {
    mpfr::mul_z;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Integer;
    MulIntegerRef MulOwnedIntegerRef
}
#[cfg(feature = "integer")]
arith_noncommut_float! {
    mpfr::div_z, xmpfr::z_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Integer;
    DivIntegerRef DivFromIntegerRef DivOwnedIntegerRef DivFromOwnedIntegerRef
}
#[cfg(feature = "integer")]
arith_forward_float! {
    mpfr::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowIntegerRef PowOwnedIntegerRef
}

#[cfg(feature = "rational")]
arith_commut_float! {
    mpfr::add_q;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Rational;
    AddRationalRef AddOwnedRationalRef
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::sub_q, xmpfr::q_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Rational;
    SubRationalRef SubFromRationalRef
        SubOwnedRationalRef SubFromOwnedRationalRef
}
#[cfg(feature = "rational")]
arith_commut_float! {
    mpfr::mul_q;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Rational;
    MulRationalRef MulOwnedRationalRef
}
#[cfg(feature = "rational")]
arith_noncommut_float! {
    mpfr::div_q, xmpfr::q_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Rational;
    DivRationalRef DivFromRationalRef
        DivOwnedRationalRef DivFromOwnedRationalRef
}

macro_rules! arith_prim_exact_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_exact_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_commut_float {
    {
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident
    } => {
        arith_prim_commut_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref
        }
    }
}

macro_rules! arith_prim_noncommut_float {
    {
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $FromRef:ident
    } => {
        arith_prim_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $FromRef
        }
    }
}

macro_rules! arith_ops {
    {
        $T:ty,
        ($AddRef:ident $add:path,
         $SubRef:ident $sub:path,
         $SubFromRef:ident $sub_from:path),
        ($MulRef:ident $mul:path,
         $DivRef:ident $div: path,
         $DivFromRef:ident $div_from:path)
    } => {
        arith_prim_commut_float! {
            $add;
            Add add;
            AddAssign add_assign;
            AddAssignRound add_assign_round;
            AddFrom add_from;
            AddFromRound add_from_round;
            $T;
            $AddRef
        }
        arith_prim_noncommut_float! {
            $sub, $sub_from;
            Sub sub;
            SubAssign sub_assign;
            SubAssignRound sub_assign_round;
            SubFrom sub_from;
            SubFromRound sub_from_round;
            $T;
            $SubRef $SubFromRef
        }
        arith_prim_commut_float! {
            $mul;
            Mul mul;
            MulAssign mul_assign;
            MulAssignRound mul_assign_round;
            MulFrom mul_from;
            MulFromRound mul_from_round;
            $T;
            $MulRef
        }
        arith_prim_noncommut_float! {
            $div, $div_from;
            Div div;
            DivAssign div_assign;
            DivAssignRound div_assign_round;
            DivFrom div_from;
            DivFromRound div_from_round;
            $T;
            $DivRef $DivFromRef
        }
    }
}

arith_ops! {
    i32,
    (AddI32Ref mpfr::add_si,
     SubI32Ref mpfr::sub_si,
     SubFromI32Ref mpfr::si_sub),
    (MulI32Ref mpfr::mul_si,
     DivI32Ref mpfr::div_si,
     DivFromI32Ref mpfr::si_div)
}
arith_ops! {
    u32,
    (AddU32Ref mpfr::add_ui,
     SubU32Ref mpfr::sub_ui,
     SubFromU32Ref mpfr::ui_sub),
    (MulU32Ref mpfr::mul_ui,
     DivU32Ref mpfr::div_ui,
     DivFromU32Ref mpfr::ui_div)
}
arith_ops! {
    f32,
    (AddF32Ref xmpfr::add_f32,
     SubF32Ref xmpfr::sub_f32,
     SubFromF32Ref xmpfr::f32_sub),
    (MulF32Ref xmpfr::mul_f32,
     DivF32Ref xmpfr::div_f32,
     DivFromF32Ref xmpfr::f32_div)
}
arith_ops! {
    f64,
    (AddF64Ref mpfr::add_d,
     SubF64Ref mpfr::sub_d,
     SubFromF64Ref mpfr::d_sub),
    (MulF64Ref mpfr::mul_d,
     DivF64Ref mpfr::div_d,
     DivFromF64Ref mpfr::d_div)
}

arith_prim_exact_float! {
    mpfr::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlU32Ref
}
arith_prim_exact_float! {
    mpfr::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrU32Ref
}
arith_prim_noncommut_float!{
    mpfr::pow_ui, mpfr::ui_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    u32;
    PowU32Ref PowFromU32Ref
}
arith_prim_exact_float! {
    mpfr::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlI32Ref
}
arith_prim_exact_float! {
    mpfr::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrI32Ref
}
arith_prim_noncommut_float!{
    mpfr::pow_si, xmpfr::si_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    i32;
    PowI32Ref PowFromI32Ref
}
arith_prim_noncommut_float!{
    xmpfr::pow_f64, xmpfr::f64_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f64;
    PowF64Ref PowFromF64Ref
}
arith_prim_noncommut_float!{
    xmpfr::pow_f32, xmpfr::f32_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f32;
    PowF32Ref PowFromF32Ref
}

mul_op_commut_round! {
    Float, Round => Ordering;
    add_mul, raw_round => ordering1;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    MulRef;
    AddMulRef
}
mul_op_noncommut_round! {
    Float, Round => Ordering;
    sub_mul, mul_sub, raw_round => ordering1;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    MulRef;
    SubMulRef SubMulFromRef
}

impl<'a> Add for MulRef<'a> {
    type Output = MulAddMulRef<'a>;
    #[inline]
    fn add(self, rhs: MulRef<'a>) -> MulAddMulRef<'a> {
        MulAddMulRef { lhs: self, rhs }
    }
}

#[derive(Clone, Copy)]
pub struct MulAddMulRef<'a> {
    lhs: MulRef<'a>,
    rhs: MulRef<'a>,
}

impl<'a> AssignRound<MulAddMulRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: MulAddMulRef<'a>,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fmma(
                self.inner_mut(),
                src.lhs.lhs.inner(),
                src.lhs.rhs.inner(),
                src.rhs.lhs.inner(),
                src.rhs.rhs.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

impl<'a> Sub for MulRef<'a> {
    type Output = MulSubMulRef<'a>;
    #[inline]
    fn sub(self, rhs: MulRef<'a>) -> MulSubMulRef<'a> {
        MulSubMulRef { lhs: self, rhs }
    }
}

#[derive(Clone, Copy)]
pub struct MulSubMulRef<'a> {
    lhs: MulRef<'a>,
    rhs: MulRef<'a>,
}

impl<'a> AssignRound<MulSubMulRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: MulSubMulRef<'a>,
        round: Round,
    ) -> Ordering {
        let ret = unsafe {
            mpfr::fmms(
                self.inner_mut(),
                src.lhs.lhs.inner(),
                src.lhs.rhs.inner(),
                src.rhs.lhs.inner(),
                src.rhs.rhs.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

unsafe fn add_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulRef,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::fma(rop, mul.lhs.inner(), mul.rhs.inner(), add, rnd)
}

unsafe fn sub_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulRef,
    rnd: mpfr::rnd_t,
) -> c_int {
    xmpfr::submul(rop, add, (mul.lhs.inner(), mul.rhs.inner()), rnd)
}

unsafe fn mul_sub(
    rop: *mut mpfr_t,
    mul: MulRef,
    sub: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::fms(rop, mul.lhs.inner(), mul.rhs.inner(), sub, rnd)
}

// use Float::sum instead of fold! for iterator sum, to get correct rounding

impl Sum for Float {
    #[inline]
    fn sum<I>(mut iter: I) -> Float
    where
        I: Iterator<Item = Float>,
    {
        match iter.next() {
            Some(first) => {
                let others = iter.collect::<Vec<_>>();
                first + Float::sum(others.iter())
            }
            None => Float::with_val(53, Special::Zero),
        }
    }
}

impl<'a> Sum<&'a Float> for Float {
    #[inline]
    fn sum<I>(mut iter: I) -> Float
    where
        I: Iterator<Item = &'a Float>,
    {
        match iter.next() {
            Some(first) => first.clone() + Float::sum(iter),
            None => Float::with_val(53, Special::Zero),
        }
    }
}

fold! { Float, Product product, Float::with_val(53, 1), Mul::mul }

#[cfg(test)]
mod tests {
    use {Assign, Float};
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    use ops::Pow;
    #[cfg(feature = "integer")]
    use std::str::FromStr;

    fn same(a: Float, b: Float) -> bool {
        if a.is_nan() && b.is_nan() {
            return true;
        }
        if a == b {
            return true;
        }
        if a.prec() == b.prec() {
            return false;
        }
        a == Float::with_val(a.prec(), b)
    }

    #[test]
    fn check_ref_op() {
        let lhs = Float::with_val(53, 12.25);
        let rhs = Float::with_val(53, -1.375);
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Float::with_val(53, -&lhs), -lhs.clone());
        assert_eq!(Float::with_val(53, &lhs + &rhs), lhs.clone() + &rhs);
        assert_eq!(Float::with_val(53, &lhs - &rhs), lhs.clone() - &rhs);
        assert_eq!(Float::with_val(53, &lhs * &rhs), lhs.clone() * &rhs);
        assert_eq!(Float::with_val(53, &lhs / &rhs), lhs.clone() / &rhs);
        assert_eq!(
            Float::with_val(53, (&lhs).pow(&rhs)),
            lhs.clone().pow(&rhs)
        );

        assert_eq!(Float::with_val(53, &lhs + pu), lhs.clone() + pu);
        assert_eq!(Float::with_val(53, &lhs - pu), lhs.clone() - pu);
        assert_eq!(Float::with_val(53, &lhs * pu), lhs.clone() * pu);
        assert_eq!(Float::with_val(53, &lhs / pu), lhs.clone() / pu);
        assert_eq!(Float::with_val(53, &lhs << pu), lhs.clone() << pu);
        assert_eq!(Float::with_val(53, &lhs >> pu), lhs.clone() >> pu);
        assert_eq!(Float::with_val(53, (&lhs).pow(pu)), lhs.clone().pow(pu));

        assert_eq!(Float::with_val(53, pu + &lhs), pu + lhs.clone());
        assert_eq!(Float::with_val(53, pu - &lhs), pu - lhs.clone());
        assert_eq!(Float::with_val(53, pu * &lhs), pu * lhs.clone());
        assert_eq!(Float::with_val(53, pu / &lhs), pu / lhs.clone());
        assert_eq!(
            Float::with_val(53, Pow::pow(pu, &lhs)),
            Pow::pow(pu, lhs.clone())
        );

        assert_eq!(Float::with_val(53, &lhs + pi), lhs.clone() + pi);
        assert_eq!(Float::with_val(53, &lhs - pi), lhs.clone() - pi);
        assert_eq!(Float::with_val(53, &lhs * pi), lhs.clone() * pi);
        assert_eq!(Float::with_val(53, &lhs / pi), lhs.clone() / pi);
        assert_eq!(Float::with_val(53, &lhs << pi), lhs.clone() << pi);
        assert_eq!(Float::with_val(53, &lhs >> pi), lhs.clone() >> pi);
        assert_eq!(Float::with_val(53, (&lhs).pow(pi)), lhs.clone().pow(pi));

        assert_eq!(Float::with_val(53, pi + &lhs), pi + lhs.clone());
        assert_eq!(Float::with_val(53, pi - &lhs), pi - lhs.clone());
        assert_eq!(Float::with_val(53, pi * &lhs), pi * lhs.clone());
        assert_eq!(Float::with_val(53, pi / &lhs), pi / lhs.clone());

        assert_eq!(Float::with_val(53, &lhs + ps), lhs.clone() + ps);
        assert_eq!(Float::with_val(53, &lhs - ps), lhs.clone() - ps);
        assert_eq!(Float::with_val(53, &lhs * ps), lhs.clone() * ps);
        assert_eq!(Float::with_val(53, &lhs / ps), lhs.clone() / ps);

        assert_eq!(Float::with_val(53, ps + &lhs), ps + lhs.clone());
        assert_eq!(Float::with_val(53, ps - &lhs), ps - lhs.clone());
        assert_eq!(Float::with_val(53, ps * &lhs), ps * lhs.clone());
        assert_eq!(Float::with_val(53, ps / &lhs), ps / lhs.clone());

        assert_eq!(Float::with_val(53, &lhs + pd), lhs.clone() + pd);
        assert_eq!(Float::with_val(53, &lhs - pd), lhs.clone() - pd);
        assert_eq!(Float::with_val(53, &lhs * pd), lhs.clone() * pd);
        assert_eq!(Float::with_val(53, &lhs / pd), lhs.clone() / pd);

        assert_eq!(Float::with_val(53, pd + &lhs), pd + lhs.clone());
        assert_eq!(Float::with_val(53, pd - &lhs), pd - lhs.clone());
        assert_eq!(Float::with_val(53, pd * &lhs), pd * lhs.clone());
        assert_eq!(Float::with_val(53, pd / &lhs), pd / lhs.clone());
    }

    #[test]
    fn check_arith_others() {
        use tests::{F32, F64, I32, I64, U32, U64};
        let large = &[
            Float::with_val(20, Special::Zero),
            Float::with_val(20, Special::NegZero),
            Float::with_val(20, Special::Infinity),
            Float::with_val(20, Special::NegInfinity),
            Float::with_val(20, Special::Nan),
            Float::with_val(20, 1),
            Float::with_val(20, -1),
            Float::with_val(20, 999999e100),
            Float::with_val(20, 999999e-100),
            Float::with_val(20, -999999e100),
            Float::with_val(20, -999999e-100),
        ];
        #[cfg(feature = "integer")]
        let z = [
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        #[cfg(feature = "rational")]
        let q = [
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];

        let against = (large.iter().cloned())
            .chain(U32.iter().map(|&x| Float::with_val(20, x)))
            .chain(I32.iter().map(|&x| Float::with_val(20, x)))
            .chain(U64.iter().map(|&x| Float::with_val(20, x)))
            .chain(I64.iter().map(|&x| Float::with_val(20, x)))
            .chain(F32.iter().map(|&x| Float::with_val(20, x)))
            .chain(F64.iter().map(|&x| Float::with_val(20, x)))
            .collect::<Vec<Float>>();
        #[cfg(feature = "integer")]
        let mut against = against;
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Float::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Float::with_val(20, x)));

        for op in U32 {
            let fop = Float::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &fop));
                assert!(same(b.clone() - *op, b.clone() - &fop));
                assert!(same(b.clone() * *op, b.clone() * &fop));
                assert!(same(b.clone() / *op, b.clone() / &fop));
                assert!(same(*op + b.clone(), fop.clone() + b));
                assert!(same(*op - b.clone(), fop.clone() - b));
                assert!(same(*op * b.clone(), fop.clone() * b));
                assert!(same(*op / b.clone(), fop.clone() / b));
            }
        }
        for op in I32 {
            let fop = Float::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &fop));
                assert!(same(b.clone() - *op, b.clone() - &fop));
                assert!(same(b.clone() * *op, b.clone() * &fop));
                assert!(same(b.clone() / *op, b.clone() / &fop));
                assert!(same(*op + b.clone(), fop.clone() + b));
                assert!(same(*op - b.clone(), fop.clone() - b));
                assert!(same(*op * b.clone(), fop.clone() * b));
                assert!(same(*op / b.clone(), fop.clone() / b));
            }
        }
        for op in F32 {
            let fop = Float::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &fop));
                assert!(same(b.clone() - *op, b.clone() - &fop));
                assert!(same(b.clone() * *op, b.clone() * &fop));
                assert!(same(b.clone() / *op, b.clone() / &fop));
                assert!(same(*op + b.clone(), fop.clone() + b));
                assert!(same(*op - b.clone(), fop.clone() - b));
                assert!(same(*op * b.clone(), fop.clone() * b));
                assert!(same(*op / b.clone(), fop.clone() / b));
            }
        }
        for op in F64 {
            let fop = Float::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &fop));
                assert!(same(b.clone() - *op, b.clone() - &fop));
                assert!(same(b.clone() * *op, b.clone() * &fop));
                assert!(same(b.clone() / *op, b.clone() / &fop));
                assert!(same(*op + b.clone(), fop.clone() + b));
                assert!(same(*op - b.clone(), fop.clone() - b));
                assert!(same(*op * b.clone(), fop.clone() * b));
                assert!(same(*op / b.clone(), fop.clone() / b));
            }
        }
        #[cfg(feature = "integer")]
        for op in &z {
            let fop = Float::with_val(100, op);
            for b in &against {
                assert!(same(b.clone() + op, b.clone() + &fop));
                assert!(same(b.clone() - op, b.clone() - &fop));
                assert!(same(b.clone() * op, b.clone() * &fop));
                assert!(same(b.clone() / op, b.clone() / &fop));
                assert!(same(op.clone() + b.clone(), fop.clone() + b));
                assert!(same(op.clone() - b.clone(), fop.clone() - b));
                assert!(same(op.clone() * b.clone(), fop.clone() * b));
                assert!(same(op.clone() / b.clone(), fop.clone() / b));
            }
        }
        #[cfg(feature = "rational")]
        for op in &q {
            let fop = Float::with_val(100, op);
            for b in &against {
                assert!(same(b.clone() + op, b.clone() + &fop));
                assert!(same(b.clone() - op, b.clone() - &fop));
                assert!(same(b.clone() * op, b.clone() * &fop));
                assert!(same(b.clone() / op, b.clone() / &fop));
                assert!(same(op.clone() + b.clone(), fop.clone() + b));
                assert!(same(op.clone() - b.clone(), fop.clone() - b));
                assert!(same(op.clone() * b.clone(), fop.clone() * b));
                assert!(same(op.clone() / b.clone(), fop.clone() / b));
            }
        }
    }

    #[test]
    fn check_sum() {
        let nothing = Vec::<Float>::new();
        let empty1: Float = nothing.iter().sum();
        assert_eq!(empty1, 0);
        assert_eq!(empty1.prec(), 53);
        let empty2: Float = nothing.into_iter().sum();
        assert_eq!(empty2, 0);

        let values = vec![
            Float::with_val(4, 5.0),
            Float::with_val(4, 1024.0),
            Float::with_val(4, -1024.0),
            Float::with_val(4, -4.5),
        ];
        let sum1: Float = values.iter().sum();
        assert_eq!(sum1, 0.5);
        assert_eq!(sum1.prec(), 4);
        let mut sum2 = Float::new(4);
        sum2.assign(Float::sum(values.iter()));
        assert_eq!(sum2, 0.5);
        sum2 += Float::sum(values.iter());
        assert_eq!(sum2, 1.0);
        let sum3: Float = values.into_iter().sum();
        assert_eq!(sum3, 0.5);
    }
}
