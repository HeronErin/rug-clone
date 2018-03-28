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
use float::Round;
use float::big::{raw_round, ordering1};
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use inner::{Inner, InnerMut};
use ops::{AddAssignRound, AddFrom, AddFromRound, AssignRound, DivAssignRound,
          DivFrom, DivFromRound, MulAssignRound, MulFrom, MulFromRound,
          NegAssign, Pow, PowAssign, PowAssignRound, PowFrom, PowFromRound,
          SubAssignRound, SubFrom, SubFromRound};
use std::{i32, u32};
use std::cmp::Ordering;
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
    type Output = NegIncomplete<'a>;
    #[inline]
    fn neg(self) -> NegIncomplete<'a> {
        NegIncomplete { val: self }
    }
}

#[derive(Debug)]
pub struct NegIncomplete<'a> {
    val: &'a Float,
}

impl<'a> AssignRound<NegIncomplete<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NegIncomplete, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::neg(
                self.inner_mut(),
                src.val.inner(),
                raw_round(round),
            )
        };
        ordering1(ret)
    }
}

macro_rules! arith_binary_self_float {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $Incomplete: ident
    ) => {
        arith_binary_self_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Incomplete
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! arith_forward_float {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident
    ) => {
        arith_forward_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete $OwnedIncomplete
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! arith_commut_float {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident
    ) => {
        arith_commut_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Incomplete $OwnedIncomplete
        }
    };
}

#[cfg(feature = "integer")]
macro_rules! arith_noncommut_float {
    (
        $func: path, $func_from: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $FromIncomplete: ident;
        $OwnedIncomplete: ident $FromOwnedIncomplete: ident
    ) => {
        arith_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Incomplete $FromIncomplete;
            $OwnedIncomplete $FromOwnedIncomplete
        }
    };
}

arith_binary_self_float! {
    mpfr::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddIncomplete
}
arith_binary_self_float! {
    mpfr::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubIncomplete
}
arith_binary_self_float! {
    mpfr::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulIncomplete
}
arith_binary_self_float! {
    mpfr::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivIncomplete
}
arith_binary_self_float! {
    mpfr::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowIncomplete
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
    AddIntegerIncomplete AddOwnedIntegerIncomplete
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
    SubIntegerIncomplete SubFromIntegerIncomplete;
    SubOwnedIntegerIncomplete SubFromOwnedIntegerIncomplete
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
    MulIntegerIncomplete MulOwnedIntegerIncomplete
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
    DivIntegerIncomplete DivFromIntegerIncomplete;
    DivOwnedIntegerIncomplete DivFromOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_forward_float! {
    mpfr::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowIntegerIncomplete PowOwnedIntegerIncomplete
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
    AddRationalIncomplete AddOwnedRationalIncomplete
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
    SubRationalIncomplete SubFromRationalIncomplete;
    SubOwnedRationalIncomplete SubFromOwnedRationalIncomplete
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
    MulRationalIncomplete MulOwnedRationalIncomplete
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
    DivRationalIncomplete DivFromRationalIncomplete;
    DivOwnedRationalIncomplete DivFromOwnedRationalIncomplete
}

macro_rules! arith_prim_exact_float {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_exact_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Incomplete
        }
    };
}

macro_rules! arith_prim_commut_float {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_commut_round! {
            Float, Round => Ordering;
            $func, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Incomplete
        }
    };
}

macro_rules! arith_prim_noncommut_float {
    (
        $func: path, $func_from: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $ImpFrom: ident $method_from: ident;
        $ImpFromRound: ident $method_from_round: ident;
        $T: ty;
        $Incomplete: ident $FromIncomplete: ident
    ) => {
        arith_prim_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, raw_round => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Incomplete $FromIncomplete
        }
    };
}

macro_rules! arith_ops {
    (
        $T: ty,
        ($AddIncomplete: ident $add: path,
         $SubIncomplete: ident $sub: path,
         $SubFromIncomplete: ident $sub_from: path),
        ($MulIncomplete: ident $mul: path,
         $DivIncomplete: ident $div: path,
         $DivFromIncomplete: ident $div_from: path)
    ) => {
        arith_prim_commut_float! {
            $add;
            Add add;
            AddAssign add_assign;
            AddAssignRound add_assign_round;
            AddFrom add_from;
            AddFromRound add_from_round;
            $T;
            $AddIncomplete
        }
        arith_prim_noncommut_float! {
            $sub, $sub_from;
            Sub sub;
            SubAssign sub_assign;
            SubAssignRound sub_assign_round;
            SubFrom sub_from;
            SubFromRound sub_from_round;
            $T;
            $SubIncomplete $SubFromIncomplete
        }
        arith_prim_commut_float! {
            $mul;
            Mul mul;
            MulAssign mul_assign;
            MulAssignRound mul_assign_round;
            MulFrom mul_from;
            MulFromRound mul_from_round;
            $T;
            $MulIncomplete
        }
        arith_prim_noncommut_float! {
            $div, $div_from;
            Div div;
            DivAssign div_assign;
            DivAssignRound div_assign_round;
            DivFrom div_from;
            DivFromRound div_from_round;
            $T;
            $DivIncomplete $DivFromIncomplete
        }
    };
}

arith_ops! {
    i32,
    (AddI32Incomplete mpfr::add_si,
     SubI32Incomplete mpfr::sub_si,
     SubFromI32Incomplete mpfr::si_sub),
    (MulI32Incomplete mpfr::mul_si,
     DivI32Incomplete mpfr::div_si,
     DivFromI32Incomplete mpfr::si_div)
}
arith_ops! {
    u32,
    (AddU32Incomplete mpfr::add_ui,
     SubU32Incomplete mpfr::sub_ui,
     SubFromU32Incomplete mpfr::ui_sub),
    (MulU32Incomplete mpfr::mul_ui,
     DivU32Incomplete mpfr::div_ui,
     DivFromU32Incomplete mpfr::ui_div)
}
arith_ops! {
    f32,
    (AddF32Incomplete xmpfr::add_f32,
     SubF32Incomplete xmpfr::sub_f32,
     SubFromF32Incomplete xmpfr::f32_sub),
    (MulF32Incomplete xmpfr::mul_f32,
     DivF32Incomplete xmpfr::div_f32,
     DivFromF32Incomplete xmpfr::f32_div)
}
arith_ops! {
    f64,
    (AddF64Incomplete mpfr::add_d,
     SubF64Incomplete mpfr::sub_d,
     SubFromF64Incomplete mpfr::d_sub),
    (MulF64Incomplete mpfr::mul_d,
     DivF64Incomplete mpfr::div_d,
     DivFromF64Incomplete mpfr::d_div)
}

arith_prim_exact_float! {
    mpfr::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlU32Incomplete
}
arith_prim_exact_float! {
    mpfr::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrU32Incomplete
}
arith_prim_noncommut_float! {
    mpfr::pow_ui, mpfr::ui_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    u32;
    PowU32Incomplete PowFromU32Incomplete
}
arith_prim_exact_float! {
    mpfr::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlI32Incomplete
}
arith_prim_exact_float! {
    mpfr::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrI32Incomplete
}
arith_prim_noncommut_float! {
    mpfr::pow_si, xmpfr::si_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    i32;
    PowI32Incomplete PowFromI32Incomplete
}
arith_prim_noncommut_float! {
    xmpfr::pow_f64, xmpfr::f64_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f64;
    PowF64Incomplete PowFromF64Incomplete
}
arith_prim_noncommut_float! {
    xmpfr::pow_f32, xmpfr::f32_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f32;
    PowF32Incomplete PowFromF32Incomplete
}

mul_op_commut_round! {
    Float, Round => Ordering;
    add_mul, raw_round => ordering1;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    MulIncomplete;
    AddMulIncomplete
}
mul_op_noncommut_round! {
    Float, Round => Ordering;
    sub_mul, mul_sub, raw_round => ordering1;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    MulIncomplete;
    SubMulIncomplete SubMulFromIncomplete
}

impl<'a> Add for MulIncomplete<'a> {
    type Output = MulAddMulIncomplete<'a>;
    #[inline]
    fn add(self, rhs: MulIncomplete<'a>) -> MulAddMulIncomplete {
        MulAddMulIncomplete { lhs: self, rhs }
    }
}

#[derive(Debug)]
pub struct MulAddMulIncomplete<'a> {
    lhs: MulIncomplete<'a>,
    rhs: MulIncomplete<'a>,
}

impl<'a> AssignRound<MulAddMulIncomplete<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: MulAddMulIncomplete,
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

impl<'a> Sub for MulIncomplete<'a> {
    type Output = MulSubMulIncomplete<'a>;
    #[inline]
    fn sub(self, rhs: MulIncomplete<'a>) -> MulSubMulIncomplete {
        MulSubMulIncomplete { lhs: self, rhs }
    }
}

#[derive(Debug)]
pub struct MulSubMulIncomplete<'a> {
    lhs: MulIncomplete<'a>,
    rhs: MulIncomplete<'a>,
}

impl<'a> AssignRound<MulSubMulIncomplete<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(
        &mut self,
        src: MulSubMulIncomplete,
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

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn add_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulIncomplete,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::fma(rop, mul.lhs.inner(), mul.rhs.inner(), add, rnd)
}

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn sub_mul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    mul: MulIncomplete,
    rnd: mpfr::rnd_t,
) -> c_int {
    xmpfr::submul(
        rop,
        add,
        (mul.lhs.inner(), mul.rhs.inner()),
        rnd,
    )
}

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn mul_sub(
    rop: *mut mpfr_t,
    mul: MulIncomplete,
    sub: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::fms(rop, mul.lhs.inner(), mul.rhs.inner(), sub, rnd)
}

#[cfg(test)]
pub(crate) mod tests {
    use Float;
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    use ops::Pow;
    #[cfg(feature = "integer")]
    use std::str::FromStr;

    pub fn same(a: Float, b: Float) -> bool {
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

    macro_rules! test_ref_op {
        ($first: expr, $second: expr) => {
            assert_eq!(
                Float::with_val(53, $first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Float::with_val(53, 12.25);
        let rhs = Float::with_val(53, -1.375);
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        test_ref_op!(-&lhs, -lhs.clone());
        test_ref_op!(&lhs + &rhs, lhs.clone() + &rhs);
        test_ref_op!(&lhs - &rhs, lhs.clone() - &rhs);
        test_ref_op!(&lhs * &rhs, lhs.clone() * &rhs);
        test_ref_op!(&lhs / &rhs, lhs.clone() / &rhs);
        test_ref_op!((&lhs).pow(&rhs), lhs.clone().pow(&rhs));

        test_ref_op!(&lhs + pu, lhs.clone() + pu);
        test_ref_op!(&lhs - pu, lhs.clone() - pu);
        test_ref_op!(&lhs * pu, lhs.clone() * pu);
        test_ref_op!(&lhs / pu, lhs.clone() / pu);
        test_ref_op!(&lhs << pu, lhs.clone() << pu);
        test_ref_op!(&lhs >> pu, lhs.clone() >> pu);
        test_ref_op!((&lhs).pow(pu), lhs.clone().pow(pu));

        test_ref_op!(pu + &lhs, pu + lhs.clone());
        test_ref_op!(pu - &lhs, pu - lhs.clone());
        test_ref_op!(pu * &lhs, pu * lhs.clone());
        test_ref_op!(pu / &lhs, pu / lhs.clone());
        test_ref_op!(Pow::pow(pu, &lhs), Pow::pow(pu, lhs.clone()));

        test_ref_op!(&lhs + pi, lhs.clone() + pi);
        test_ref_op!(&lhs - pi, lhs.clone() - pi);
        test_ref_op!(&lhs * pi, lhs.clone() * pi);
        test_ref_op!(&lhs / pi, lhs.clone() / pi);
        test_ref_op!(&lhs << pi, lhs.clone() << pi);
        test_ref_op!(&lhs >> pi, lhs.clone() >> pi);
        test_ref_op!((&lhs).pow(pi), lhs.clone().pow(pi));

        test_ref_op!(pi + &lhs, pi + lhs.clone());
        test_ref_op!(pi - &lhs, pi - lhs.clone());
        test_ref_op!(pi * &lhs, pi * lhs.clone());
        test_ref_op!(pi / &lhs, pi / lhs.clone());

        test_ref_op!(&lhs + ps, lhs.clone() + ps);
        test_ref_op!(&lhs - ps, lhs.clone() - ps);
        test_ref_op!(&lhs * ps, lhs.clone() * ps);
        test_ref_op!(&lhs / ps, lhs.clone() / ps);

        test_ref_op!(ps + &lhs, ps + lhs.clone());
        test_ref_op!(ps - &lhs, ps - lhs.clone());
        test_ref_op!(ps * &lhs, ps * lhs.clone());
        test_ref_op!(ps / &lhs, ps / lhs.clone());

        test_ref_op!(&lhs + pd, lhs.clone() + pd);
        test_ref_op!(&lhs - pd, lhs.clone() - pd);
        test_ref_op!(&lhs * pd, lhs.clone() * pd);
        test_ref_op!(&lhs / pd, lhs.clone() / pd);

        test_ref_op!(pd + &lhs, pd + lhs.clone());
        test_ref_op!(pd - &lhs, pd - lhs.clone());
        test_ref_op!(pd * &lhs, pd * lhs.clone());
        test_ref_op!(pd / &lhs, pd / lhs.clone());
    }

    #[test]
    fn check_arith_others() {
        use tests::{F32, F64, I32, I64, U32, U64};
        #[cfg(int_128)]
        use tests::{I128, U128};
        let large = [
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

        let against = large
            .iter()
            .cloned()
            .chain(U32.iter().map(|&x| Float::with_val(20, x)))
            .chain(I32.iter().map(|&x| Float::with_val(20, x)))
            .chain(U64.iter().map(|&x| Float::with_val(20, x)))
            .chain(I64.iter().map(|&x| Float::with_val(20, x)))
            .chain(F32.iter().map(|&x| Float::with_val(20, x)))
            .chain(F64.iter().map(|&x| Float::with_val(20, x)))
            .collect::<Vec<Float>>();
        #[cfg(any(int_128, feature = "integer"))]
        let mut against = against;
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Float::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Float::with_val(20, x)));
        #[cfg(int_128)]
        {
            against.extend(U128.iter().map(|&x| Float::with_val(20, x)));
            against.extend(I128.iter().map(|&x| Float::with_val(20, x)));
        }

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
                assert!(same(op + b.clone(), fop.clone() + b));
                assert!(same(op - b.clone(), fop.clone() - b));
                assert!(same(op * b.clone(), fop.clone() * b));
                assert!(same(op / b.clone(), fop.clone() / b));
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
                assert!(same(op + b.clone(), fop.clone() + b));
                assert!(same(op - b.clone(), fop.clone() - b));
                assert!(same(op * b.clone(), fop.clone() * b));
                assert!(same(op / b.clone(), fop.clone() / b));
            }
        }
    }
}
