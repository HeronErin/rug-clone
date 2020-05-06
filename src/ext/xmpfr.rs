// Copyright © 2016–2020 University of Malta

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

use crate::{
    float::{Round, SmallFloat, Special},
    misc::NegAbs,
    ops::NegAssign,
    Float,
};
use az::CheckedAs;
use core::{cmp::Ordering, mem::MaybeUninit};
#[cfg(feature = "rational")]
use gmp_mpfr_sys::gmp::mpq_t;
use gmp_mpfr_sys::{
    gmp::limb_t,
    mpfr::{self, exp_t, mpfr_t, prec_t, rnd_t},
};
use libc::{c_int, c_void};
#[cfg(feature = "integer")]
use {
    crate::{float, misc::AsOrPanic},
    core::cmp,
    gmp_mpfr_sys::gmp::{self, mpz_t},
};

pub trait OptFloat: Copy {
    const IS_SOME: bool;
    fn mpfr(self) -> *const mpfr_t;
    fn mpfr_or(self, default: *mut mpfr_t) -> *const mpfr_t;
}

impl OptFloat for () {
    const IS_SOME: bool = false;
    #[inline(always)]
    fn mpfr(self) -> *const mpfr_t {
        panic!("unwrapping ()");
    }
    #[inline(always)]
    fn mpfr_or(self, default: *mut mpfr_t) -> *const mpfr_t {
        default as *const mpfr_t
    }
}

impl OptFloat for &Float {
    const IS_SOME: bool = true;
    #[inline(always)]
    fn mpfr(self) -> *const mpfr_t {
        self.as_raw()
    }
    #[inline(always)]
    fn mpfr_or(self, _default: *mut mpfr_t) -> *const mpfr_t {
        self.as_raw()
    }
}

#[inline]
pub fn raw_round(round: Round) -> rnd_t {
    match round {
        Round::Nearest => rnd_t::RNDN,
        Round::Zero => rnd_t::RNDZ,
        Round::Up => rnd_t::RNDU,
        Round::Down => rnd_t::RNDD,
        _ => unreachable!(),
    }
}

#[inline]
pub fn ordering1(ord: c_int) -> Ordering {
    ord.cmp(&0)
}

#[inline]
fn ordering2(ord: c_int) -> (Ordering, Ordering) {
    // ord == first + 4 * second
    let first = match ord & 3 {
        2 => -1,
        0 => 0,
        1 => 1,
        _ => unreachable!(),
    };
    let second = match ord >> 2 {
        2 => -1,
        0 => 0,
        1 => 1,
        _ => unreachable!(),
    };
    (ordering1(first), ordering1(second))
}

macro_rules! wrap {
    (fn $fn:ident($($op:ident: $O:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn<$($O: OptFloat),*>(
            rop: &mut Float,
            $($op: $O,)*
            $($param: $T,)*
            rnd: Round,
        ) -> Ordering {
            let rop = rop.as_raw_mut();
            $(let $op = $op.mpfr_or(rop);)*
            ordering1(unsafe { $deleg(rop, $($op,)* $($param.into(),)* raw_round(rnd)) })
        }
    };
}

macro_rules! wrap0 {
    (fn $fn:ident($($param:ident: $T:ty),*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Float,
            $($param: $T,)*
            rnd: Round,
        ) -> Ordering {
            ordering1(unsafe {
                $deleg(
                    rop.as_raw_mut(),
                    $($param.into(),)*
                    raw_round(rnd),
                )
            })
        }
    };
}

#[inline]
pub fn si_pow_ui(rop: &mut Float, base: i32, exponent: u32, rnd: Round) -> Ordering {
    let (base_neg, base_abs) = base.neg_abs();
    if !base_neg || (exponent & 1) == 0 {
        ordering1(unsafe {
            mpfr::ui_pow_ui(
                rop.as_raw_mut(),
                base_abs.into(),
                exponent.into(),
                raw_round(rnd),
            )
        })
    } else {
        let reverse_rnd = match rnd {
            Round::Up => Round::Down,
            Round::Down => Round::Up,
            unchanged => unchanged,
        };
        let reverse_ord = ordering1(unsafe {
            mpfr::ui_pow_ui(
                rop.as_raw_mut(),
                base_abs.into(),
                exponent.into(),
                raw_round(reverse_rnd),
            )
        });
        neg(rop, (), Round::Nearest);
        reverse_ord.reverse()
    }
}

// do not use mpfr::neg for op is () to avoid function call
#[inline]
pub fn neg<O: OptFloat>(rop: &mut Float, op: O, rnd: Round) -> Ordering {
    if O::IS_SOME {
        ordering1(unsafe { mpfr::neg(rop.as_raw_mut(), op.mpfr(), raw_round(rnd)) })
    } else {
        unsafe {
            rop.inner_mut().sign.neg_assign();
            if rop.is_nan() {
                mpfr::set_nanflag();
            }
            Ordering::Equal
        }
    }
}

#[inline]
pub fn signum<O: OptFloat>(rop: &mut Float, op: O, _rnd: Round) -> Ordering {
    let rop = rop.as_raw_mut();
    let op = op.mpfr_or(rop);
    ordering1(unsafe {
        if mpfr::nan_p(op) != 0 {
            mpfr::set(rop, op, rnd_t::RNDZ)
        } else if mpfr::signbit(op) != 0 {
            mpfr::set_si(rop, -1, rnd_t::RNDZ)
        } else {
            mpfr::set_si(rop, 1, rnd_t::RNDZ)
        }
    })
}

#[inline]
pub fn recip<O: OptFloat>(rop: &mut Float, op: O, rnd: Round) -> Ordering {
    let rop = rop.as_raw_mut();
    let op = op.mpfr_or(rop);
    ordering1(unsafe { mpfr::ui_div(rop, 1, op, raw_round(rnd)) })
}

#[inline]
pub fn jn<O: OptFloat>(rop: &mut Float, op: O, n: i32, rnd: Round) -> Ordering {
    let rop = rop.as_raw_mut();
    let op = op.mpfr_or(rop);
    ordering1(unsafe { mpfr::jn(rop, n.into(), op, raw_round(rnd)) })
}

#[inline]
pub fn yn<O: OptFloat>(rop: &mut Float, op: O, n: i32, rnd: Round) -> Ordering {
    let rop = rop.as_raw_mut();
    let op = op.mpfr_or(rop);
    ordering1(unsafe { mpfr::yn(rop, n.into(), op, raw_round(rnd)) })
}

#[inline]
pub fn sin_cos<O: OptFloat>(
    rop_sin: &mut Float,
    rop_cos: &mut Float,
    op: O,
    rnd: Round,
) -> (Ordering, Ordering) {
    let rop_sin = rop_sin.as_raw_mut();
    let rop_cos = rop_cos.as_raw_mut();
    let op = op.mpfr_or(rop_sin);
    ordering2(unsafe { mpfr::sin_cos(rop_sin, rop_cos, op, raw_round(rnd)) })
}

#[inline]
pub fn sinh_cosh<O: OptFloat>(
    rop_sin: &mut Float,
    rop_cos: &mut Float,
    op: O,
    rnd: Round,
) -> (Ordering, Ordering) {
    let rop_sin = rop_sin.as_raw_mut();
    let rop_cos = rop_cos.as_raw_mut();
    let op = op.mpfr_or(rop_sin);
    ordering2(unsafe { mpfr::sinh_cosh(rop_sin, rop_cos, op, raw_round(rnd)) })
}

#[inline]
pub fn modf<O: OptFloat>(
    rop_i: &mut Float,
    rop_f: &mut Float,
    op: O,
    rnd: Round,
) -> (Ordering, Ordering) {
    let rop_i = rop_i.as_raw_mut();
    let rop_f = rop_f.as_raw_mut();
    let op = op.mpfr_or(rop_i);
    ordering2(unsafe { mpfr::modf(rop_i, rop_f, op, raw_round(rnd)) })
}

wrap! { fn remainder(x: O, y: P) -> mpfr::remainder }
wrap0! { fn ui_pow_ui(base: u32, exponent: u32) -> mpfr::ui_pow_ui }
wrap0! { fn ui_2exp(ui: u32, exponent: i32) -> mpfr::set_ui_2exp }
wrap0! { fn si_2exp(si: i32, exponent: i32) -> mpfr::set_si_2exp }
wrap! { fn copysign(op1: O, op2: P) -> mpfr::copysign }
wrap! { fn sqr(op: O) -> mpfr::sqr }
wrap! { fn sqrt(op: O) -> mpfr::sqrt }
wrap0! { fn sqrt_ui(u: u32) -> mpfr::sqrt_ui }
wrap! { fn rec_sqrt(op: O) -> mpfr::rec_sqrt }
wrap! { fn cbrt(op: O) -> mpfr::cbrt }
wrap! { fn rootn_ui(op: O; k: u32) -> mpfr::rootn_ui }
wrap! { fn abs(op: O) -> mpfr::abs }
wrap! { fn min(op1: O, op2: P) -> mpfr::min }
wrap! { fn max(op1: O, op2: P) -> mpfr::max }
wrap! { fn dim(op1: O, op2: P) -> mpfr::dim }
wrap! { fn log(op: O) -> mpfr::log }
wrap0! { fn log_ui(u: u32) -> mpfr::log_ui }
wrap! { fn log2(op: O) -> mpfr::log2 }
wrap! { fn log10(op: O) -> mpfr::log10 }
wrap! { fn exp(op: O) -> mpfr::exp }
wrap! { fn exp2(op: O) -> mpfr::exp2 }
wrap! { fn exp10(op: O) -> mpfr::exp10 }
wrap! { fn sin(op: O) -> mpfr::sin }
wrap! { fn cos(op: O) -> mpfr::cos }
wrap! { fn tan(op: O) -> mpfr::tan }
wrap! { fn sec(op: O) -> mpfr::sec }
wrap! { fn csc(op: O) -> mpfr::csc }
wrap! { fn cot(op: O) -> mpfr::cot }
wrap! { fn acos(op: O) -> mpfr::acos }
wrap! { fn asin(op: O) -> mpfr::asin }
wrap! { fn atan(op: O) -> mpfr::atan }
wrap! { fn atan2(y: O, x: P) -> mpfr::atan2 }
wrap! { fn cosh(op: O) -> mpfr::cosh }
wrap! { fn sinh(op: O) -> mpfr::sinh }
wrap! { fn tanh(op: O) -> mpfr::tanh }
wrap! { fn sech(op: O) -> mpfr::sech }
wrap! { fn csch(op: O) -> mpfr::csch }
wrap! { fn coth(op: O) -> mpfr::coth }
wrap! { fn acosh(op: O) -> mpfr::acosh }
wrap! { fn asinh(op: O) -> mpfr::asinh }
wrap! { fn atanh(op: O) -> mpfr::atanh }
wrap0! { fn fac_ui(n: u32) -> mpfr::fac_ui }
wrap! { fn log1p(op: O) -> mpfr::log1p }
wrap! { fn expm1(op: O) -> mpfr::expm1 }
wrap! { fn eint(op: O) -> mpfr::eint }
wrap! { fn li2(op: O) -> mpfr::li2 }
wrap! { fn gamma(op: O) -> mpfr::gamma }
wrap! { fn gamma_inc(op1: O, op2: P) -> mpfr::gamma_inc }
wrap! { fn lngamma(op: O) -> mpfr::lngamma }
wrap! { fn digamma(op: O) -> mpfr::digamma }
wrap! { fn zeta(op: O) -> mpfr::zeta }
wrap0! { fn zeta_ui(u: u32) -> mpfr::zeta_ui }
wrap! { fn erf(op: O) -> mpfr::erf }
wrap! { fn erfc(op: O) -> mpfr::erfc }
wrap! { fn j0(op: O) -> mpfr::j0 }
wrap! { fn j1(op: O) -> mpfr::j1 }
wrap! { fn y0(op: O) -> mpfr::y0 }
wrap! { fn y1(op: O) -> mpfr::y1 }
wrap! { fn agm(op1: O, op2: P) -> mpfr::agm }
wrap! { fn hypot(x: O, y: P) -> mpfr::hypot }
wrap! { fn ai(op: O) -> mpfr::ai }
wrap! { fn rint_ceil(op: O) -> mpfr::rint_ceil }
wrap! { fn rint_floor(op: O) -> mpfr::rint_floor }
wrap! { fn rint_round(op: O) -> mpfr::rint_round }
wrap! { fn rint_roundeven(op: O) -> mpfr::rint_roundeven }
wrap! { fn rint_trunc(op: O) -> mpfr::rint_trunc }
wrap! { fn frac(op: O) -> mpfr::frac }

#[cfg(feature = "integer")]
#[inline]
pub unsafe fn z_div(r: *mut mpfr_t, lhs: *const mpz_t, rhs: *const mpfr_t, rnd: rnd_t) -> c_int {
    divf_mulz_divz(r, rhs, Some(lhs), None, rnd)
}

#[cfg(feature = "rational")]
#[inline]
pub unsafe fn q_sub(r: *mut mpfr_t, lhs: *const mpq_t, rhs: *const mpfr_t, rnd: rnd_t) -> c_int {
    let flip_rnd = match rnd {
        rnd_t::RNDU => rnd_t::RNDD,
        rnd_t::RNDD => rnd_t::RNDU,
        unchanged => unchanged,
    };
    let flip_ret = -mpfr::sub_q(r, rhs, lhs, flip_rnd);
    if mpfr::zero_p(r) == 0 {
        // the negation here is exact
        mpfr::neg(r, r, rnd_t::RNDN);
    }
    -flip_ret
}

#[cfg(feature = "rational")]
#[inline]
pub unsafe fn q_div(r: *mut mpfr_t, lhs: *const mpq_t, rhs: *const mpfr_t, rnd: rnd_t) -> c_int {
    let lhs_num = gmp::mpq_numref_const(lhs);
    let lhs_den = gmp::mpq_denref_const(lhs);
    divf_mulz_divz(r, rhs, Some(lhs_num), Some(lhs_den), rnd)
}

#[cfg(feature = "integer")]
// mul and div must must form a canonical rational, except that div
// can be negative
unsafe fn divf_mulz_divz(
    rop: *mut mpfr_t,
    f: *const mpfr_t,
    mul: Option<*const mpz_t>,
    div: Option<*const mpz_t>,
    rnd: rnd_t,
) -> c_int {
    let mul_size = mul.map(|i| (*i).size);
    let div_size = div.map(|i| (*i).size);
    if mul_size == Some(0) {
        mpfr::ui_div(rop, 0, f, rnd);
        if let Some(s) = div_size {
            if s < 0 {
                (*rop).sign = -(*rop).sign;
            }
        }
        return 0;
    }
    if div_size == Some(0) {
        mpfr::mul_ui(rop, f, 0, rnd);
        mpfr::ui_div(rop, 1, rop, rnd);
        if let Some(s) = mul_size {
            if s < 0 {
                (*rop).sign = -(*rop).sign;
            }
        }
        return 0;
    }

    let mut denom_buf: Float;
    let denom = if let Some(div) = div {
        let mut prec = (*f).prec.as_or_panic::<u32>();
        let bits = gmp::mpz_sizeinbase(div, 2).as_or_panic::<u32>();
        prec = prec.checked_add(bits).expect("overflow");
        denom_buf = Float::new(prec);
        mpfr::mul_z(denom_buf.as_raw_mut(), f, div, rnd_t::RNDN);
        denom_buf.as_raw()
    } else {
        f
    };
    if let Some(mul) = mul {
        let bits = gmp::mpz_sizeinbase(mul, 2).as_or_panic::<u32>();
        let mut buf = Float::new(cmp::max(float::prec_min(), bits));
        mpfr::set_z(buf.as_raw_mut(), mul, rnd);
        mpfr::div(rop, buf.as_raw(), denom, rnd)
    } else {
        mpfr::ui_div(rop, 1, denom, rnd)
    }
}

pub unsafe fn get_f32(op: *const mpfr_t, rnd: rnd_t) -> f32 {
    let mut limb: limb_t = 0;
    let mut single = MaybeUninit::uninit();
    custom_zero(single.as_mut_ptr(), &mut limb, 24);
    let mut single = single.assume_init();
    mpfr::set(&mut single, op, rnd);
    let val = mpfr::get_d(&single, rnd);
    val as f32
}

#[inline]
pub unsafe fn set_f32(rop: *mut mpfr_t, op: f32, rnd: rnd_t) -> c_int {
    set_f64(rop, op.into(), rnd)
}

#[inline]
pub unsafe fn set_f64(rop: *mut mpfr_t, op: f64, rnd: rnd_t) -> c_int {
    // retain sign in case of NaN
    let sign_neg = op.is_sign_negative();
    let ret = mpfr::set_d(rop, op, rnd);
    if sign_neg {
        (*rop).sign = -1;
    }
    ret
}

#[inline]
pub unsafe fn set_i128(rop: *mut mpfr_t, val: i128, rnd: rnd_t) -> c_int {
    let small = SmallFloat::from(val);
    mpfr::set(rop, small.as_raw(), rnd)
}

#[inline]
pub unsafe fn set_u128(rop: *mut mpfr_t, val: u128, rnd: rnd_t) -> c_int {
    let small = SmallFloat::from(val);
    mpfr::set(rop, small.as_raw(), rnd)
}

#[inline]
pub unsafe fn cmp_i64(op1: *const mpfr_t, op2: i64) -> c_int {
    if let Some(op2) = op2.checked_as() {
        mpfr::cmp_si(op1, op2)
    } else {
        let small = SmallFloat::from(op2);
        mpfr::cmp(op1, small.as_raw())
    }
}

#[inline]
pub unsafe fn cmp_u64(op1: *const mpfr_t, op2: u64) -> c_int {
    if let Some(op2) = op2.checked_as() {
        mpfr::cmp_ui(op1, op2)
    } else {
        let small = SmallFloat::from(op2);
        mpfr::cmp(op1, small.as_raw())
    }
}

#[inline]
pub unsafe fn cmp_i128(op1: *const mpfr_t, op2: i128) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::cmp(op1, small.as_raw())
}

#[inline]
pub unsafe fn cmp_u128(op1: *const mpfr_t, op2: u128) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::cmp(op1, small.as_raw())
}

#[inline]
pub unsafe fn cmp_u32_2exp(op1: *const mpfr_t, op2: u32, e: i32) -> c_int {
    mpfr::cmp_ui_2exp(op1, op2.into(), e.into())
}

#[inline]
pub unsafe fn cmp_i32_2exp(op1: *const mpfr_t, op2: i32, e: i32) -> c_int {
    mpfr::cmp_si_2exp(op1, op2.into(), e.into())
}

#[inline]
pub unsafe fn submul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    (m1, m2): (*const mpfr_t, *const mpfr_t),
    rnd: rnd_t,
) -> c_int {
    let reverse_rnd = match rnd {
        rnd_t::RNDU => rnd_t::RNDD,
        rnd_t::RNDD => rnd_t::RNDU,
        unchanged => unchanged,
    };
    let reverse_ord = mpfr::fms(rop, m1, m2, add, reverse_rnd);
    (*rop).sign = -(*rop).sign;
    -reverse_ord
}

#[inline]
pub unsafe fn custom_zero(f: *mut mpfr_t, limbs: *mut limb_t, prec: prec_t) {
    mpfr::custom_init(limbs as *mut c_void, prec);
    mpfr::custom_init_set(f, mpfr::ZERO_KIND, 0, prec, limbs as *mut c_void);
}

#[inline]
pub unsafe fn custom_regular(f: *mut mpfr_t, limbs: *mut limb_t, exp: exp_t, prec: prec_t) {
    mpfr::custom_init(limbs as *mut c_void, prec);
    mpfr::custom_init_set(f, mpfr::REGULAR_KIND, exp, prec, limbs as *mut c_void);
}

#[inline]
pub unsafe fn custom_special(f: *mut mpfr_t, limbs: *mut limb_t, special: Special, prec: prec_t) {
    mpfr::custom_init(limbs as *mut c_void, prec);
    let kind = match special {
        Special::Zero => mpfr::ZERO_KIND,
        Special::NegZero => -mpfr::ZERO_KIND,
        Special::Infinity => mpfr::INF_KIND,
        Special::NegInfinity => -mpfr::INF_KIND,
        Special::Nan => mpfr::NAN_KIND,
        _ => unreachable!(),
    };
    mpfr::custom_init_set(f, kind, 0, prec, limbs as *mut c_void);
}

pub const EXP_ZERO: mpfr::exp_t = -mpfr::exp_t::max_value();

#[inline]
pub unsafe fn shl_u32(rop: *mut mpfr_t, op1: *const mpfr_t, op2: u32, rnd: rnd_t) -> c_int {
    mpfr::mul_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_u32(rop: *mut mpfr_t, op1: *const mpfr_t, op2: u32, rnd: rnd_t) -> c_int {
    mpfr::div_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shl_i32(rop: *mut mpfr_t, op1: *const mpfr_t, op2: i32, rnd: rnd_t) -> c_int {
    mpfr::mul_2si(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_i32(rop: *mut mpfr_t, op1: *const mpfr_t, op2: i32, rnd: rnd_t) -> c_int {
    mpfr::div_2si(rop, op1, op2.into(), rnd)
}
