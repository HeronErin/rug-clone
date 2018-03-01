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
#[cfg(feature = "rational")]
use Rational;
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
    type Output = NegIncomplete<'a>;
    #[inline]
    fn neg(self) -> NegIncomplete<'a> {
        NegIncomplete { val: self }
    }
}

#[derive(Debug)]
pub struct NegIncomplete<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<NegIncomplete<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(
        &mut self,
        src: NegIncomplete<'a>,
        round: Round2,
    ) -> Ordering2 {
        let ret = unsafe {
            mpc::neg(
                self.inner_mut(),
                src.val.inner(),
                raw_round2(round),
            )
        };
        ordering2(ret)
    }
}

macro_rules! arith_binary_self_complex {
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
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $ImpFrom $method_from;
            $ImpFromRound $method_from_round;
            $Incomplete
        }
    };
}

macro_rules! arith_forward_complex {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident $OwnedIncomplete: ident
    ) => {
        arith_forward_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete $OwnedIncomplete
        }
    };
}

macro_rules! arith_commut_complex {
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
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
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

macro_rules! arith_noncommut_complex {
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
            Complex, Round2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
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

arith_binary_self_complex! {
    mpc::add;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    AddIncomplete
}
arith_binary_self_complex! {
    mpc::sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    SubIncomplete
}
arith_binary_self_complex! {
    mpc::mul;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    MulIncomplete
}
arith_binary_self_complex! {
    mpc::div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    DivIncomplete
}
arith_binary_self_complex! {
    mpc::pow;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    PowFrom pow_from;
    PowFromRound pow_from_round;
    PowIncomplete
}

arith_commut_complex! {
    mpc::add_fr;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Float;
    AddFloatIncomplete AddOwnedFloatIncomplete
}
arith_noncommut_complex! {
    mpc::sub_fr, mpc::fr_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    Float;
    SubFloatIncomplete SubFromFloatIncomplete;
    SubOwnedFloatIncomplete SubFromOwnedFloatIncomplete
}
arith_commut_complex! {
    mpc::mul_fr;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Float;
    MulFloatIncomplete MulOwnedFloatIncomplete
}
arith_noncommut_complex! {
    mpc::div_fr, mpc::fr_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    Float;
    DivFloatIncomplete DivFromFloatIncomplete;
    DivOwnedFloatIncomplete DivFromOwnedFloatIncomplete
}
arith_forward_complex! {
    mpc::pow_fr;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Float;
    PowFloatIncomplete PowOwnedFloatIncomplete
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    mpc::pow_z;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    Integer;
    PowIntegerIncomplete PowOwnedIntegerIncomplete
}

macro_rules! arith_prim_complex {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $ImpAssignRound: ident $method_assign_round: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $ImpAssignRound $method_assign_round;
            $T;
            $Incomplete
        }
    };
}

macro_rules! arith_prim_exact_complex {
    (
        $func: path;
        $Imp: ident $method: ident;
        $ImpAssign: ident $method_assign: ident;
        $T: ty;
        $Incomplete: ident
    ) => {
        arith_prim_exact_round! {
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
            $Imp $method;
            $ImpAssign $method_assign;
            $T;
            $Incomplete
        }
    };
}

macro_rules! arith_prim_commut_complex {
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
            Complex, Round2 => Ordering2;
            $func, raw_round2 => ordering2;
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

macro_rules! arith_prim_noncommut_complex {
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
            Complex, Round2 => Ordering2;
            $func, $func_from, raw_round2 => ordering2;
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

arith_prim_commut_complex! {
    xmpc::add_ui;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    u32;
    AddU32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::sub_ui, xmpc::ui_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    u32;
    SubU32Incomplete SubFromU32Incomplete
}
arith_prim_commut_complex! {
    xmpc::mul_ui;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    u32;
    MulU32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::div_ui, xmpc::ui_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    u32;
    DivU32Incomplete DivFromU32Incomplete
}
arith_prim_commut_complex! {
    xmpc::add_si;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    i32;
    AddI32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::sub_si, xmpc::si_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    i32;
    SubI32Incomplete SubFromI32Incomplete
}
arith_prim_commut_complex! {
    xmpc::mul_si;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    i32;
    MulI32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::div_si, xmpc::si_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    i32;
    DivI32Incomplete DivFromI32Incomplete
}
arith_prim_commut_complex! {
    xmpc::add_f32;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    f32;
    AddF32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::sub_f32, xmpc::f32_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    f32;
    SubF32Incomplete SubFromF32Incomplete
}
arith_prim_commut_complex! {
    xmpc::mul_f32;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    f32;
    MulF32Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::div_f32, xmpc::f32_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    f32;
    DivF32Incomplete DivFromF32Incomplete
}
arith_prim_commut_complex! {
    xmpc::add_f64;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    f64;
    AddF64Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::sub_f64, xmpc::f64_sub;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    f64;
    SubF64Incomplete SubFromF64Incomplete
}
arith_prim_commut_complex! {
    xmpc::mul_f64;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    f64;
    MulF64Incomplete
}
arith_prim_noncommut_complex! {
    xmpc::div_f64, xmpc::f64_div;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    DivFrom div_from;
    DivFromRound div_from_round;
    f64;
    DivF64Incomplete DivFromF64Incomplete
}

#[cfg(feature = "integer")]
arith_commut_complex! {
    xmpc::add_z;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Integer;
    AddIntegerIncomplete AddOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_noncommut_complex! {
    xmpc::sub_z, xmpc::z_sub;
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
arith_commut_complex! {
    xmpc::mul_z;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Integer;
    MulIntegerIncomplete MulOwnedIntegerIncomplete
}
#[cfg(feature = "integer")]
arith_forward_complex! {
    xmpc::div_z;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    Integer;
    DivIntegerIncomplete DivOwnedIntegerIncomplete
}
#[cfg(feature = "rational")]
arith_commut_complex! {
    xmpc::add_q;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    Rational;
    AddRationalIncomplete AddOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_noncommut_complex! {
    xmpc::sub_q, xmpc::q_sub;
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
arith_commut_complex! {
    xmpc::mul_q;
    Mul mul;
    MulAssign mul_assign;
    MulAssignRound mul_assign_round;
    MulFrom mul_from;
    MulFromRound mul_from_round;
    Rational;
    MulRationalIncomplete MulOwnedRationalIncomplete
}
#[cfg(feature = "rational")]
arith_forward_complex! {
    xmpc::div_q;
    Div div;
    DivAssign div_assign;
    DivAssignRound div_assign_round;
    Rational;
    DivRationalIncomplete DivOwnedRationalIncomplete
}

arith_prim_exact_complex! {
    mpc::mul_2ui;
    Shl shl;
    ShlAssign shl_assign;
    u32;
    ShlU32Incomplete
}
arith_prim_exact_complex! {
    mpc::div_2ui;
    Shr shr;
    ShrAssign shr_assign;
    u32;
    ShrU32Incomplete
}
arith_prim_complex! {
    mpc::pow_ui;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    u32;
    PowU32Incomplete
}
arith_prim_exact_complex! {
    mpc::mul_2si;
    Shl shl;
    ShlAssign shl_assign;
    i32;
    ShlI32Incomplete
}
arith_prim_exact_complex! {
    mpc::div_2si;
    Shr shr;
    ShrAssign shr_assign;
    i32;
    ShrI32Incomplete
}
arith_prim_complex! {
    mpc::pow_si;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    i32;
    PowI32Incomplete
}
arith_prim_complex! {
    mpc::pow_d;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f64;
    PowF64Incomplete
}
arith_prim_complex! {
    xmpc::pow_f32;
    Pow pow;
    PowAssign pow_assign;
    PowAssignRound pow_assign_round;
    f32;
    PowF32Incomplete
}

mul_op_commut_round! {
    Complex, Round2 => Ordering2;
    add_mul, raw_round2 => ordering2;
    Add add;
    AddAssign add_assign;
    AddAssignRound add_assign_round;
    AddFrom add_from;
    AddFromRound add_from_round;
    MulIncomplete;
    AddMulIncomplete
}
mul_op_noncommut_round! {
    Complex, Round2 => Ordering2;
    sub_mul, mul_sub, raw_round2 => ordering2;
    Sub sub;
    SubAssign sub_assign;
    SubAssignRound sub_assign_round;
    SubFrom sub_from;
    SubFromRound sub_from_round;
    MulIncomplete;
    SubMulIncomplete SubMulFromIncomplete
}

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn add_mul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    mul: MulIncomplete,
    rnd: mpc::rnd_t,
) -> c_int {
    mpc::fma(rop, mul.lhs.inner(), mul.rhs.inner(), add, rnd)
}

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn sub_mul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    mul: MulIncomplete,
    rnd: mpc::rnd_t,
) -> c_int {
    xmpc::submul(
        rop,
        add,
        (mul.lhs.inner(), mul.rhs.inner()),
        rnd,
    )
}

#[allow(unknown_lints, needless_pass_by_value)]
unsafe fn mul_sub(
    rop: *mut mpc_t,
    mul: MulIncomplete,
    sub: *const mpc_t,
    rnd: mpc::rnd_t,
) -> c_int {
    xmpc::mulsub(
        rop,
        (mul.lhs.inner(), mul.rhs.inner()),
        sub,
        rnd,
    )
}

#[cfg(test)]
mod tests {
    use {Complex, Float};
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    use float::arith::tests as float_tests;
    use ops::Pow;
    #[cfg(feature = "integer")]
    use std::str::FromStr;

    fn same(a: Complex, b: Complex) -> bool {
        let (re_a, im_a) = a.into_real_imag();
        let (re_b, im_b) = b.into_real_imag();
        float_tests::same(re_a, re_b) && float_tests::same(im_a, im_b)
    }

    macro_rules! test_ref_op {
        ($first: expr, $second: expr) => {
            assert_eq!(
                Complex::with_val(53, $first),
                $second,
                "({}) != ({})",
                stringify!($first),
                stringify!($second)
            );
        };
    }

    #[test]
    fn check_ref_op() {
        let lhs = Complex::with_val(53, (12.25, -1.375));
        let rhs = Complex::with_val(53, (-1.375, 13));
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

        test_ref_op!((&lhs).pow(ps), lhs.clone().pow(ps));
        test_ref_op!((&lhs).pow(pd), lhs.clone().pow(pd));
    }

    #[test]
    fn check_arith_others() {
        use tests::{F32, F64, I32, I64, U32, U64};
        let large = [
            Complex::with_val(20, (Special::Zero, 1.0)),
            Complex::with_val(20, (Special::NegZero, 1.0)),
            Complex::with_val(20, (Special::Infinity, 1.0)),
            Complex::with_val(20, (Special::NegInfinity, 1.0)),
            Complex::with_val(20, (Special::Nan, 1.0)),
            Complex::with_val(20, (1, 1.0)),
            Complex::with_val(20, (-1, 1.0)),
            Complex::with_val(20, (999999e100, 1.0)),
            Complex::with_val(20, (999999e-100, 1.0)),
            Complex::with_val(20, (-999999e100, 1.0)),
            Complex::with_val(20, (-999999e-100, 1.0)),
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
        let f = [
            Float::with_val(20, 0.0),
            Float::with_val(20, 1.0),
            Float::with_val(20, -1.0),
            Float::with_val(20, 12.5),
            Float::with_val(20, 12.5) << 10000,
            Float::with_val(20, Special::Infinity),
        ];

        let mut against = large
            .iter()
            .cloned()
            .chain(U32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(I32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(U64.iter().map(|&x| Complex::with_val(20, x)))
            .chain(I64.iter().map(|&x| Complex::with_val(20, x)))
            .chain(F32.iter().map(|&x| Complex::with_val(20, x)))
            .chain(F64.iter().map(|&x| Complex::with_val(20, x)))
            .collect::<Vec<Complex>>();
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Complex::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Complex::with_val(20, x)));
        against.extend(f.iter().map(|x| Complex::with_val(20, x)));

        for op in U32 {
            let cop = Complex::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &cop));
                assert!(same(*op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - *op, b.clone() - &cop));
                assert!(same(*op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * *op, b.clone() * &cop));
                    assert!(same(*op * b.clone(), cop.clone() * b));
                    if *op != 0 {
                        assert!(same(b.clone() / *op, b.clone() / &cop));
                    }
                    if *b != 0i32 {
                        assert!(same(*op / b.clone(), cop.clone() / b));
                    }
                }
            }
        }
        for op in I32 {
            let cop = Complex::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &cop));
                assert!(same(*op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - *op, b.clone() - &cop));
                assert!(same(*op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * *op, b.clone() * &cop));
                    assert!(same(*op * b.clone(), cop.clone() * b));
                    if *op != 0 {
                        assert!(same(b.clone() / *op, b.clone() / &cop));
                    }
                    if *b != 0i32 {
                        assert!(same(*op / b.clone(), cop.clone() / b));
                    }
                }
            }
        }
        for op in F32 {
            let cop = Complex::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &cop));
                assert!(same(*op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - *op, b.clone() - &cop));
                assert!(same(*op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * *op, b.clone() * &cop));
                    assert!(same(*op * b.clone(), cop.clone() * b));
                    if *op != 0.0 {
                        assert!(same(b.clone() / *op, b.clone() / &cop));
                    }
                    if *b != 0i32 {
                        assert!(same(*op / b.clone(), cop.clone() / b));
                    }
                }
            }
        }
        for op in F64 {
            let cop = Complex::with_val(100, *op);
            for b in &against {
                assert!(same(b.clone() + *op, b.clone() + &cop));
                assert!(same(*op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - *op, b.clone() - &cop));
                assert!(same(*op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * *op, b.clone() * &cop));
                    assert!(same(*op * b.clone(), cop.clone() * b));
                    if *op != 0.0 {
                        assert!(same(b.clone() / *op, b.clone() / &cop));
                    }
                    if *b != 0i32 {
                        assert!(same(*op / b.clone(), cop.clone() / b));
                    }
                }
            }
        }
        #[cfg(feature = "integer")]
        for op in &z {
            let cop = Complex::with_val(100, op);
            for b in &against {
                assert!(same(b.clone() + op, b.clone() + &cop));
                assert!(same(op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - op, b.clone() - &cop));
                assert!(same(op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * op, b.clone() * &cop));
                    assert!(same(op * b.clone(), cop.clone() * b));
                    if *op != 0 {
                        assert!(same(b.clone() / op, b.clone() / &cop));
                    }
                }
            }
        }
        #[cfg(feature = "rational")]
        for op in &q {
            let cop = Complex::with_val(100, op);
            for b in &against {
                assert!(same(b.clone() + op, b.clone() + &cop));
                assert!(same(op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - op, b.clone() - &cop));
                assert!(same(op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * op, b.clone() * &cop));
                    assert!(same(op * b.clone(), cop.clone() * b));
                    if *op != 0 {
                        assert!(same(b.clone() / op, b.clone() / &cop));
                    }
                }
            }
        }
        for op in &f {
            let cop = Complex::with_val(100, op);
            for b in &against {
                assert!(same(b.clone() + op, b.clone() + &cop));
                assert!(same(op + b.clone(), cop.clone() + b));
                assert!(same(b.clone() - op, b.clone() - &cop));
                assert!(same(op - b.clone(), cop.clone() - b));
                if b.real().is_finite() && b.imag().is_finite() {
                    assert!(same(b.clone() * op, b.clone() * &cop));
                    assert!(same(op * b.clone(), cop.clone() * b));
                    if *op != 0 {
                        assert!(same(b.clone() / op, b.clone() / &cop));
                    }
                    if *b != 0i32 {
                        assert!(same(op / b.clone(), cop.clone() / b));
                    }
                }
            }
        }
    }
}
