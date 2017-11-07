// Copyright © 2016–2017 University of Malta

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
use big_float::{rraw, ordering1};
use ext::mpfr as xmpfr;
use float::Round;
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
            mpfr::neg(self.inner_mut(), self.inner(), rraw(Round::Nearest));
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

pub struct NegRef<'a> {
    val: &'a Float,
}

impl<'a> AssignRound<NegRef<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: NegRef<'a>, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::neg(self.inner_mut(), src.val.inner(), rraw(round))
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
            $func, rraw => ordering1;
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
        $Ref:ident $RefOwn:ident
    } => {
        arith_forward_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $RefOwn
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
        $Ref:ident $RefOwn:ident
    } => {
        arith_commut_round! {
            Float, Round => Ordering;
            $func, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefOwn
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
        $Ref:ident $RefFrom:ident $RefOwn:ident $RefFromOwn:ident
    } => {
        arith_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefFrom $RefOwn $RefFromOwn
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
    AddRefInteger AddRefIntegerOwn
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
    SubRefInteger SubFromRefInteger SubRefIntegerOwn SubFromRefIntegerOwn
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
    MulRefInteger MulRefIntegerOwn
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
    DivRefInteger DivFromRefInteger DivRefIntegerOwn DivFromRefIntegerOwn
}
#[cfg(feature = "integer")]
arith_forward_float! {
    mpfr::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowRefInteger PowRefIntegerOwn
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
    AddRefRational AddRefRationalOwn
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
    SubRefRational SubFromRefRational SubRefRationalOwn SubFromRefRationalOwn
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
    MulRefRational MulRefRationalOwn
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
    DivRefRational DivFromRefRational DivRefRationalOwn DivFromRefRationalOwn
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
            $func, rraw => ordering1;
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
            $func, rraw => ordering1;
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
        $Ref:ident $RefFrom:ident
    } => {
        arith_prim_noncommut_round! {
            Float, Round => Ordering;
            $func, $func_from, rraw => ordering1;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $RefFrom
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
    (AddRefI32 mpfr::add_si,
     SubRefI32 mpfr::sub_si,
     SubFromRefI32 mpfr::si_sub),
    (MulRefI32 mpfr::mul_si,
     DivRefI32 mpfr::div_si,
     DivFromRefI32 mpfr::si_div)
}
arith_ops! {
    u32,
    (AddRefU32 mpfr::add_ui,
     SubRefU32 mpfr::sub_ui,
     SubFromRefU32 mpfr::ui_sub),
    (MulRefU32 mpfr::mul_ui,
     DivRefU32 mpfr::div_ui,
     DivFromRefU32 mpfr::ui_div)
}
arith_ops! {
    f32,
    (AddRefF32 xmpfr::add_f32,
     SubRefF32 xmpfr::sub_f32,
     SubFromRefF32 xmpfr::f32_sub),
    (MulRefF32 xmpfr::mul_f32,
     DivRefF32 xmpfr::div_f32,
     DivFromRefF32 xmpfr::f32_div)
}
arith_ops! {
    f64,
    (AddRefF64 mpfr::add_d,
     SubRefF64 mpfr::sub_d,
     SubFromRefF64 mpfr::d_sub),
    (MulRefF64 mpfr::mul_d,
     DivRefF64 mpfr::div_d,
     DivFromRefF64 mpfr::d_div)
}

arith_prim_exact_float! {
    mpfr::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlRefU32
}
arith_prim_exact_float! {
    mpfr::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrRefU32
}
arith_prim_noncommut_float!{
    mpfr::pow_ui, mpfr::ui_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    u32;
    PowRefU32 PowFromRefU32
}
arith_prim_exact_float! {
    mpfr::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlRefI32
}
arith_prim_exact_float! {
    mpfr::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrRefI32
}
arith_prim_noncommut_float!{
    mpfr::pow_si, xmpfr::si_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    i32;
    PowRefI32 PowFromRefI32
}
arith_prim_noncommut_float!{
    xmpfr::pow_f64, xmpfr::f64_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f64;
    PowRefF64 PowFromRefF64
}
arith_prim_noncommut_float!{
    xmpfr::pow_f32, xmpfr::f32_pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    f32;
    PowRefF32 PowFromRefF32
}

mul_op_commut_round! {
    Float, Round => Ordering;
    add_mul, rraw => ordering1;
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
    sub_mul, mul_sub, rraw => ordering1;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    MulRef;
    SubMulRef SubMulFromRef
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

sum_prod! { Float, Float::with_val(53, 0), Float::with_val(53, 1) }

#[cfg(test)]
mod tests {
    use Float;
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    use ops::Pow;
    use std::{f32, f64, i32, u32};
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
        let work_prec = 20;
        let check_prec = 100;
        let f = [
            Float::with_val(work_prec, Special::Zero),
            Float::with_val(work_prec, Special::NegZero),
            Float::with_val(work_prec, Special::Infinity),
            Float::with_val(work_prec, Special::NegInfinity),
            Float::with_val(work_prec, Special::Nan),
            Float::with_val(work_prec, 1),
            Float::with_val(work_prec, -1),
            Float::with_val(work_prec, 999999e100),
            Float::with_val(work_prec, 999999e-100),
            Float::with_val(work_prec, -999999e100),
            Float::with_val(work_prec, -999999e-100),
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
        let u = [0, 1, 1000, u32::MAX];
        let s = [i32::MIN, -1000, -1, 0, 1, 1000, i32::MAX];
        let double = [
            f64::INFINITY,
            f64::MAX,
            f64::MIN_POSITIVE,
            0.0,
            -0.0,
            -f64::MIN_POSITIVE,
            f64::MIN,
            f64::NEG_INFINITY,
            f64::NAN,
            1.0,
            2.0,
            12.0e43,
        ];
        let single = [
            f32::INFINITY,
            f32::MAX,
            f32::MIN_POSITIVE,
            0.0,
            -0.0,
            -f32::MIN_POSITIVE,
            f32::MIN,
            f32::NEG_INFINITY,
            f32::NAN,
            1.0,
            2.0,
            12.0e30,
        ];
        #[cfg(feature = "integer")]
        for zz in &z {
            let zf = Float::with_val(check_prec, zz);
            for ff in &f {
                assert!(same(ff.clone() + zz, ff.clone() + &zf));
                assert!(same(ff.clone() - zz, ff.clone() - &zf));
                assert!(same(ff.clone() * zz, ff.clone() * &zf));
                assert!(same(ff.clone() / zz, ff.clone() / &zf));
                assert!(same(zz.clone() + ff.clone(), zf.clone() + ff));
                assert!(same(zz.clone() - ff.clone(), zf.clone() - ff));
                assert!(same(zz.clone() * ff.clone(), zf.clone() * ff));
                assert!(same(zz.clone() / ff.clone(), zf.clone() / ff));
            }
        }
        #[cfg(feature = "rational")]
        for qq in &q {
            let qf = Float::with_val(check_prec, qq);
            for ff in &f {
                assert!(same(ff.clone() + qq, ff.clone() + &qf));
                assert!(same(ff.clone() - qq, ff.clone() - &qf));
                assert!(same(ff.clone() * qq, ff.clone() * &qf));
                assert!(same(ff.clone() / qq, ff.clone() / &qf));
                assert!(same(qq.clone() + ff.clone(), qf.clone() + ff));
                assert!(same(qq.clone() - ff.clone(), qf.clone() - ff));
                assert!(same(qq.clone() * ff.clone(), qf.clone() * ff));
                assert!(same(qq.clone() / ff.clone(), qf.clone() / ff));
            }
        }
        for uu in &u {
            let uf = Float::with_val(check_prec, *uu);
            for ff in &f {
                assert!(same(ff.clone() + *uu, ff.clone() + &uf));
                assert!(same(ff.clone() - *uu, ff.clone() - &uf));
                assert!(same(ff.clone() * *uu, ff.clone() * &uf));
                assert!(same(ff.clone() / *uu, ff.clone() / &uf));
                assert!(same(*uu + ff.clone(), uf.clone() + ff));
                assert!(same(*uu - ff.clone(), uf.clone() - ff));
                assert!(same(*uu * ff.clone(), uf.clone() * ff));
                assert!(same(*uu / ff.clone(), uf.clone() / ff));
            }
        }
        for ss in &s {
            let sf = Float::with_val(check_prec, *ss);
            for ff in &f {
                assert!(same(ff.clone() + *ss, ff.clone() + &sf));
                assert!(same(ff.clone() - *ss, ff.clone() - &sf));
                assert!(same(ff.clone() * *ss, ff.clone() * &sf));
                assert!(same(ff.clone() / *ss, ff.clone() / &sf));
                assert!(same(*ss + ff.clone(), sf.clone() + ff));
                assert!(same(*ss - ff.clone(), sf.clone() - ff));
                assert!(same(*ss * ff.clone(), sf.clone() * ff));
                assert!(same(*ss / ff.clone(), sf.clone() / ff));
            }
        }
        for oo in &double {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
        for oo in &single {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert!(same(ff.clone() + *oo, ff.clone() + &of));
                assert!(same(ff.clone() - *oo, ff.clone() - &of));
                assert!(same(ff.clone() * *oo, ff.clone() * &of));
                assert!(same(ff.clone() / *oo, ff.clone() / &of));
                assert!(same(*oo + ff.clone(), of.clone() + ff));
                assert!(same(*oo - ff.clone(), of.clone() - ff));
                assert!(same(*oo * ff.clone(), of.clone() * ff));
                assert!(same(*oo / ff.clone(), of.clone() / ff));
            }
        }
    }
}
