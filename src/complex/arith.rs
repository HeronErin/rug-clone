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

use {Complex, Float};
#[cfg(feature = "integer")]
use Integer;
use complex::big::{Ordering2, Round2, ordering2, raw_round2};
use ext::mpc as xmpc;
use gmp_mpfr_sys::mpc::{self, mpc_t};
use inner::{Inner, InnerMut};
use ops::{AddAssignRound, AddFrom, AddFromRound, AssignRound, DivAssignRound,
          DivFrom, DivFromRound, MulAssignRound, MulFrom, MulFromRound,
          NegAssign, Pow, PowAssign, PowAssignRound, PowFrom, PowFromRound,
          SubAssignRound, SubFrom, SubFromRound};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::c_int;

impl Neg for Complex {
    type Output = Complex;
    #[inline]
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    #[inline]
    fn neg_assign(&mut self) {
        self.mut_real().neg_assign();
        self.mut_imag().neg_assign();
    }
}

impl<'a> Neg for &'a Complex {
    type Output = NegRef<'a>;
    #[inline]
    fn neg(self) -> NegRef<'a> {
        NegRef { val: self }
    }
}

#[derive(Debug)]
pub struct NegRef<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<NegRef<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: NegRef<'a>, round: Round2) -> Ordering2 {
        let ret = unsafe {
            mpc::neg(self.inner_mut(), src.val.inner(), raw_round2(round))
        };
        ordering2(ret)
    }
}

macro_rules! arith_binary_self_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $Ref:ident
    ) => {
        arith_binary_self_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Ref
        }
    };
}

macro_rules! arith_forward_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident $OwnedRef:ident
    ) => {
        arith_forward_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref $OwnedRef
        }
    };
}

macro_rules! arith_commut_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $OwnedRef:ident
    ) => {
        arith_commut_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $OwnedRef
        }
    };
}

macro_rules! arith_noncommut_complex {
    (
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $FromRef:ident $OwnedRef:ident $FromOwnedRef:ident
    ) => {
        arith_noncommut_round! {
            Complex, Round2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $FromRef $OwnedRef $FromOwnedRef
        }
    };
}

arith_binary_self_complex! {
    mpc::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddRef
}
arith_binary_self_complex! {
    mpc::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubRef
}
arith_binary_self_complex! {
    mpc::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulRef
}
arith_binary_self_complex! {
    mpc::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivRef
}
arith_binary_self_complex! {
    mpc::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowRef
}

arith_commut_complex! {
    mpc::add_fr;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Float;
    AddFloatRef AddOwnedFloatRef
}
arith_noncommut_complex! {
    mpc::sub_fr, mpc::fr_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Float;
    SubFloatRef SubFromFloatRef SubOwnedFloatRef SubFromOwnedFloatRef
}
arith_commut_complex! {
    mpc::mul_fr;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Float;
    MulFloatRef MulOwnedFloatRef
}
arith_noncommut_complex! {
    mpc::div_fr, mpc::fr_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Float;
    DivFloatRef DivFromFloatRef DivOwnedFloatRef DivFromOwnedFloatRef
}
arith_forward_complex! {
    mpc::pow_fr;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Float;
    PowFloatRef PowOwnedFloatRef
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    mpc::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowIntegerRef PowOwnedIntegerRef
}

macro_rules! arith_prim_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $T:ty;
        $Ref:ident
    ) => {
        arith_prim_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Ref
        }
    };
}

macro_rules! arith_prim_exact_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $T:ty;
        $Ref:ident
    ) => {
        arith_prim_exact_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Ref
        }
    };
}

macro_rules! arith_prim_commut_complex {
    (
        $func:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident
    ) => {
        arith_prim_commut_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref
        }
    };
}

macro_rules! arith_prim_noncommut_complex {
    (
        $func:path, $func_from:path;
        $Imp:ident $method:ident;
        $ImpAssign:ident $method_assign:ident;
        $ImpAssignRound:ident $method_assign_round:ident;
        $ImpFrom:ident $method_from:ident;
        $ImpFromRound:ident $method_from_round:ident;
        $T:ty;
        $Ref:ident $FromRef:ident
    ) => {
        arith_prim_noncommut_round! {
            Complex, Round2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $T;
            $Ref $FromRef
        }
    };
}

arith_prim_commut_complex! {
    mpc::add_ui;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    u32;
    AddU32Ref
}
arith_prim_noncommut_complex! {
    mpc::sub_ui, xmpc::ui_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    u32;
    SubU32Ref SubFromU32Ref
}
arith_prim_commut_complex! {
    mpc::mul_ui;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    u32;
    MulU32Ref
}
arith_prim_noncommut_complex! {
    mpc::div_ui, xmpc::ui_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    u32;
    DivU32Ref DivFromU32Ref
}
arith_prim_commut_complex! {
    xmpc::add_si;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    i32;
    AddI32Ref
}
arith_prim_noncommut_complex! {
    xmpc::sub_si, xmpc::si_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    i32;
    SubI32Ref SubFromI32Ref
}
arith_prim_commut_complex! {
    mpc::mul_si;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    i32;
    MulI32Ref
}
arith_prim_noncommut_complex! {
    xmpc::div_si, xmpc::si_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    i32;
    DivI32Ref DivFromI32Ref
}

arith_prim_exact_complex! {
    mpc::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlU32Ref
}
arith_prim_exact_complex! {
    mpc::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrU32Ref
}
arith_prim_complex! {
    mpc::pow_ui;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    u32;
    PowU32Ref
}
arith_prim_exact_complex! {
    mpc::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlI32Ref
}
arith_prim_exact_complex! {
    mpc::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrI32Ref
}
arith_prim_complex! {
    mpc::pow_si;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    i32;
    PowI32Ref
}
arith_prim_complex! {
    mpc::pow_d;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f64;
    PowF64Ref
}
arith_prim_complex! {
    xmpc::pow_f32;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f32;
    PowF32Ref
}

mul_op_commut_round! {
    Complex, Round2 => Ordering2;
    add_mul, raw_round2 => ordering2;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    MulRef;
    AddMulRef
}
mul_op_noncommut_round! {
    Complex, Round2 => Ordering2;
    sub_mul, mul_sub, raw_round2 => ordering2;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    MulRef;
    SubMulRef SubMulFromRef
}

unsafe fn add_mul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    mul: MulRef,
    rnd: mpc::rnd_t,
) -> c_int {
    mpc::fma(rop, mul.lhs.inner(), mul.rhs.inner(), add, rnd)
}

unsafe fn sub_mul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    mul: MulRef,
    rnd: mpc::rnd_t,
) -> c_int {
    xmpc::submul(rop, add, (mul.lhs.inner(), mul.rhs.inner()), rnd)
}

unsafe fn mul_sub(
    rop: *mut mpc_t,
    mul: MulRef,
    sub: *const mpc_t,
    rnd: mpc::rnd_t,
) -> c_int {
    xmpc::mulsub(rop, (mul.lhs.inner(), mul.rhs.inner()), sub, rnd)
}

#[cfg(test)]
mod tests {
    use Complex;
    use ops::Pow;

    #[test]
    fn check_ref_op() {
        let lhs = Complex::with_val(53, (12.25, -1.375));
        let rhs = Complex::with_val(53, (-1.375, 13));
        let pu = 30_u32;
        let pi = -15_i32;
        let ps = 31.625_f32;
        let pd = -1.5_f64;
        assert_eq!(Complex::with_val(53, -&lhs), -lhs.clone());
        assert_eq!(Complex::with_val(53, &lhs + &rhs), lhs.clone() + &rhs);
        assert_eq!(Complex::with_val(53, &lhs - &rhs), lhs.clone() - &rhs);
        assert_eq!(Complex::with_val(53, &lhs * &rhs), lhs.clone() * &rhs);
        assert_eq!(Complex::with_val(53, &lhs / &rhs), lhs.clone() / &rhs);
        assert_eq!(
            Complex::with_val(53, (&lhs).pow(&rhs)),
            lhs.clone().pow(&rhs)
        );

        assert_eq!(Complex::with_val(53, &lhs + pu), lhs.clone() + pu);
        assert_eq!(Complex::with_val(53, &lhs - pu), lhs.clone() - pu);
        assert_eq!(Complex::with_val(53, &lhs * pu), lhs.clone() * pu);
        assert_eq!(Complex::with_val(53, &lhs / pu), lhs.clone() / pu);
        assert_eq!(Complex::with_val(53, &lhs << pu), lhs.clone() << pu);
        assert_eq!(Complex::with_val(53, &lhs >> pu), lhs.clone() >> pu);
        assert_eq!(Complex::with_val(53, (&lhs).pow(pu)), lhs.clone().pow(pu));

        assert_eq!(Complex::with_val(53, pu + &lhs), pu + lhs.clone());
        assert_eq!(Complex::with_val(53, pu - &lhs), pu - lhs.clone());
        assert_eq!(Complex::with_val(53, pu * &lhs), pu * lhs.clone());
        assert_eq!(Complex::with_val(53, pu / &lhs), pu / lhs.clone());

        assert_eq!(Complex::with_val(53, &lhs + pi), lhs.clone() + pi);
        assert_eq!(Complex::with_val(53, &lhs - pi), lhs.clone() - pi);
        assert_eq!(Complex::with_val(53, &lhs * pi), lhs.clone() * pi);
        assert_eq!(Complex::with_val(53, &lhs / pi), lhs.clone() / pi);
        assert_eq!(Complex::with_val(53, &lhs << pi), lhs.clone() << pi);
        assert_eq!(Complex::with_val(53, &lhs >> pi), lhs.clone() >> pi);
        assert_eq!(Complex::with_val(53, (&lhs).pow(pi)), lhs.clone().pow(pi));

        assert_eq!(Complex::with_val(53, pi + &lhs), pi + lhs.clone());
        assert_eq!(Complex::with_val(53, pi - &lhs), pi - lhs.clone());
        assert_eq!(Complex::with_val(53, pi * &lhs), pi * lhs.clone());
        assert_eq!(Complex::with_val(53, pi / &lhs), pi / lhs.clone());

        assert_eq!(Complex::with_val(53, (&lhs).pow(ps)), lhs.clone().pow(ps));
        assert_eq!(Complex::with_val(53, (&lhs).pow(pd)), lhs.clone().pow(pd));
    }
}
