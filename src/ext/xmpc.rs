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
    complex::SmallComplex,
    ext::xmpfr::{self, ordering1, raw_round},
    float::Round,
    Complex, Float,
};
use core::{cmp::Ordering, mem::MaybeUninit};
#[cfg(feature = "rational")]
use gmp_mpfr_sys::gmp::mpq_t;
#[cfg(feature = "integer")]
use gmp_mpfr_sys::gmp::mpz_t;
use gmp_mpfr_sys::{
    mpc::{self, mpc_t, rnd_t},
    mpfr::{self, mpfr_t, prec_t, rnd_t as mpfr_rnd_t},
};
use libc::{c_int, c_long, c_ulong};

pub trait OptComplex: Copy {
    const IS_SOME: bool;
    fn mpc(self) -> *const mpc_t;
    fn mpc_or(self, default: *mut mpc_t) -> *const mpc_t;
}

impl OptComplex for () {
    const IS_SOME: bool = false;
    #[inline(always)]
    fn mpc(self) -> *const mpc_t {
        panic!("unwrapping ()");
    }
    #[inline(always)]
    fn mpc_or(self, default: *mut mpc_t) -> *const mpc_t {
        default as *const mpc_t
    }
}

impl OptComplex for &Complex {
    const IS_SOME: bool = true;
    #[inline(always)]
    fn mpc(self) -> *const mpc_t {
        self.as_raw()
    }
    #[inline(always)]
    fn mpc_or(self, _default: *mut mpc_t) -> *const mpc_t {
        self.as_raw()
    }
}

pub type Round2 = (Round, Round);
pub const NEAREST2: Round2 = (Round::Nearest, Round::Nearest);

pub type Ordering2 = (Ordering, Ordering);

#[inline]
pub fn raw_round2(round: Round2) -> rnd_t {
    match (round.0, round.1) {
        (Round::Nearest, Round::Nearest) => mpc::RNDNN,
        (Round::Nearest, Round::Zero) => mpc::RNDNZ,
        (Round::Nearest, Round::Up) => mpc::RNDNU,
        (Round::Nearest, Round::Down) => mpc::RNDND,
        (Round::Zero, Round::Nearest) => mpc::RNDZN,
        (Round::Zero, Round::Zero) => mpc::RNDZZ,
        (Round::Zero, Round::Up) => mpc::RNDZU,
        (Round::Zero, Round::Down) => mpc::RNDZD,
        (Round::Up, Round::Nearest) => mpc::RNDUN,
        (Round::Up, Round::Zero) => mpc::RNDUZ,
        (Round::Up, Round::Up) => mpc::RNDUU,
        (Round::Up, Round::Down) => mpc::RNDUD,
        (Round::Down, Round::Nearest) => mpc::RNDDN,
        (Round::Down, Round::Zero) => mpc::RNDDZ,
        (Round::Down, Round::Up) => mpc::RNDDU,
        (Round::Down, Round::Down) => mpc::RNDDD,
        _ => unreachable!(),
    }
}

#[inline]
pub fn ordering2(ord: c_int) -> Ordering2 {
    // ord == first + 4 * second
    let first = mpc::INEX_RE(ord).cmp(&0);
    let second = mpc::INEX_IM(ord).cmp(&0);
    (first, second)
}

#[inline]
fn ordering4(ord: c_int) -> (Ordering2, Ordering2) {
    (ordering2(mpc::INEX1(ord)), ordering2(mpc::INEX2(ord)))
}

macro_rules! unsafe_wrap {
    (fn $fn:ident($($op:ident: $O:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn<$($O: OptComplex),*>(
            rop: &mut Complex,
            $($op: $O,)*
            $($param: $T,)*
            rnd: Round2,
        ) -> Ordering2 {
            let rop = rop.as_raw_mut();
            $(let $op = $op.mpc_or(rop);)*
            ordering2(unsafe { $deleg(rop, $($op,)* $($param.into(),)* raw_round2(rnd)) })
        }
    };
}

// do not use mpc::neg for op is () to avoid function call
#[inline]
pub fn neg<O: OptComplex>(rop: &mut Complex, op: O, rnd: Round2) -> Ordering2 {
    if O::IS_SOME {
        ordering2(unsafe { mpc::neg(rop.as_raw_mut(), op.mpc(), raw_round2(rnd)) })
    } else {
        (
            xmpfr::neg(rop.mut_real(), (), rnd.0),
            xmpfr::neg(rop.mut_imag(), (), rnd.1),
        )
    }
}

#[inline]
pub fn mul_i<O: OptComplex>(rop: &mut Complex, op: O, neg: bool, rnd: Round2) -> Ordering2 {
    let rop = rop.as_raw_mut();
    let op = op.mpc_or(rop);
    ordering2(unsafe { mpc::mul_i(rop, op, if neg { -1 } else { 0 }, raw_round2(rnd)) })
}

#[inline]
pub fn recip<O: OptComplex>(rop: &mut Complex, op: O, rnd: Round2) -> Ordering2 {
    let rop = rop.as_raw_mut();
    let op = op.mpc_or(rop);
    ordering2(unsafe { ui_div(rop, 1, op, raw_round2(rnd)) })
}

#[inline]
pub fn rootofunity(rop: &mut Complex, n: u32, k: u32, rnd: Round2) -> Ordering2 {
    ordering2(unsafe { mpc::rootofunity(rop.as_raw_mut(), n.into(), k.into(), raw_round2(rnd)) })
}

#[inline]
pub fn sin_cos<O: OptComplex>(
    rop_sin: &mut Complex,
    rop_cos: &mut Complex,
    op: O,
    rnd: Round2,
) -> (Ordering2, Ordering2) {
    let rop_sin = rop_sin.as_raw_mut();
    let rop_cos = rop_cos.as_raw_mut();
    let op = op.mpc_or(rop_sin);
    ordering4(unsafe { mpc::sin_cos(rop_sin, rop_cos, op, raw_round2(rnd), raw_round2(rnd)) })
}

pub fn sum<'a, I>(rop: &mut Complex, values: I, rnd: Round2) -> Ordering2
where
    I: Iterator<Item = &'a Complex>,
{
    let (real, imag) = rop.as_mut_real_imag();
    let capacity = match values.size_hint() {
        (lower, None) => lower,
        (_, Some(upper)) => upper,
    };
    let mut pointers_real = Vec::<*const mpfr_t>::with_capacity(capacity);
    let mut pointers_imag = Vec::<*const mpfr_t>::with_capacity(capacity);
    for value in values {
        pointers_real.push(value.real().as_raw());
        pointers_imag.push(value.imag().as_raw());
    }
    unsafe {
        (
            xmpfr::sum_raw(real.as_raw_mut(), &pointers_real, rnd.0),
            xmpfr::sum_raw(imag.as_raw_mut(), &pointers_imag, rnd.1),
        )
    }
}

// add original value of rop to sum
#[inline]
pub fn sum_including_old<'a, I>(rop: &mut Complex, values: I, rnd: Round2) -> Ordering2
where
    I: Iterator<Item = &'a Complex>,
{
    let (real, imag) = rop.as_mut_real_imag();
    let (real, imag) = (real.as_raw_mut(), imag.as_raw_mut());
    let capacity = match values.size_hint() {
        (lower, None) => lower + 1,
        (_, Some(upper)) => upper + 1,
    };
    let mut pointers_real = Vec::with_capacity(capacity);
    let mut pointers_imag = Vec::with_capacity(capacity);
    pointers_real.push(real as *const mpfr_t);
    pointers_imag.push(imag as *const mpfr_t);
    for value in values {
        pointers_real.push(value.real().as_raw());
        pointers_imag.push(value.imag().as_raw());
    }
    unsafe {
        (
            xmpfr::sum_raw(real, &pointers_real, rnd.0),
            xmpfr::sum_raw(imag, &pointers_imag, rnd.1),
        )
    }
}

unsafe_wrap! { fn fma(op1: O, op2: P, op3: Q) -> mpc::fma }

unsafe_wrap! { fn set(op: O) -> mpc::set }
unsafe_wrap! { fn proj(op: O) -> mpc::proj }
unsafe_wrap! { fn sqr(op: O) -> mpc::sqr }
unsafe_wrap! { fn sqrt(op: O) -> mpc::sqrt }
unsafe_wrap! { fn conj(op: O) -> mpc::conj }
unsafe_wrap! { fn log(op: O) -> mpc::log }
unsafe_wrap! { fn log10(op: O) -> mpc::log10 }
unsafe_wrap! { fn exp(op: O) -> mpc::exp }
unsafe_wrap! { fn sin(op: O) -> mpc::sin }
unsafe_wrap! { fn cos(op: O) -> mpc::cos }
unsafe_wrap! { fn tan(op: O) -> mpc::tan }
unsafe_wrap! { fn sinh(op: O) -> mpc::sinh }
unsafe_wrap! { fn cosh(op: O) -> mpc::cosh }
unsafe_wrap! { fn tanh(op: O) -> mpc::tanh }
unsafe_wrap! { fn asin(op: O) -> mpc::asin }
unsafe_wrap! { fn acos(op: O) -> mpc::acos }
unsafe_wrap! { fn atan(op: O) -> mpc::atan }
unsafe_wrap! { fn asinh(op: O) -> mpc::asinh }
unsafe_wrap! { fn acosh(op: O) -> mpc::acosh }
unsafe_wrap! { fn atanh(op: O) -> mpc::atanh }

#[inline]
pub fn write_new_nan(dst: &mut MaybeUninit<Complex>, prec_real: prec_t, prec_imag: prec_t) {
    // Safety: we can cast pointers to/from Complex/mpc_t as they are repr(transparent).
    unsafe {
        let inner_ptr = cast_ptr_mut!(dst.as_mut_ptr(), mpc_t);
        mpc::init3(inner_ptr, prec_real, prec_imag);
    }
}

#[inline]
pub fn write_real_imag(dst: &mut MaybeUninit<Complex>, real: Float, imag: Float) {
    // Safety:
    //   * We can cast pointers to/from Complex/mpc_t as they are repr(transparent).
    //   * We can cast pointers to/from Float/mpfr_t as they are repr(transparent).
    //   * realref/imagref only offset the pointers, and can operate on uninit memory.
    unsafe {
        let inner_ptr = cast_ptr_mut!(dst.as_mut_ptr(), mpc_t);
        let real_ptr = cast_ptr_mut!(mpc::realref(inner_ptr), Float);
        real_ptr.write(real);
        let imag_ptr = cast_ptr_mut!(mpc::imagref(inner_ptr), Float);
        imag_ptr.write(imag);
    }
}

#[inline]
pub fn realref_const(c: &Complex) -> &Float {
    unsafe { &*cast_ptr!(mpc::realref_const(c.as_raw()), Float) }
}

#[inline]
pub fn imagref_const(c: &Complex) -> &Float {
    unsafe { &*cast_ptr!(mpc::imagref_const(c.as_raw()), Float) }
}

#[inline]
pub fn realref(c: &mut Complex) -> &mut Float {
    unsafe { &mut *cast_ptr_mut!(mpc::realref(c.as_raw_mut()), Float) }
}

#[inline]
pub fn imagref(c: &mut Complex) -> &mut Float {
    unsafe { &mut *cast_ptr_mut!(mpc::imagref(c.as_raw_mut()), Float) }
}

#[inline]
pub fn realref_imagref(c: &mut Complex) -> (&mut Float, &mut Float) {
    let c = c.as_raw_mut();
    unsafe {
        (
            &mut *cast_ptr_mut!(mpc::realref(c), Float),
            &mut *cast_ptr_mut!(mpc::imagref(c), Float),
        )
    }
}

#[inline]
pub fn split(c: Complex) -> (Float, Float) {
    let raw = c.into_raw();
    // raw has no Drop
    unsafe { (Float::from_raw(raw.re), Float::from_raw(raw.im)) }
}

#[inline]
pub fn abs(f: &mut Float, c: &Complex, round: Round) -> Ordering {
    ordering1(unsafe { mpc::abs(f.as_raw_mut(), c.as_raw(), raw_round(round)) })
}

#[inline]
pub fn arg(f: &mut Float, c: &Complex, round: Round) -> Ordering {
    ordering1(unsafe { mpc::arg(f.as_raw_mut(), c.as_raw(), raw_round(round)) })
}

#[inline]
pub fn norm(f: &mut Float, c: &Complex, round: Round) -> Ordering {
    ordering1(unsafe { mpc::norm(f.as_raw_mut(), c.as_raw(), raw_round(round)) })
}

#[inline]
pub fn cmp_abs(op1: &Complex, op2: &Complex) -> Ordering {
    ordering1(unsafe { mpc::cmp_abs(op1.as_raw(), op2.as_raw()) })
}

macro_rules! sum_forward {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: *const mpc_t, op2: $T, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                mpfr::set(mpc::imagref(rop), mpc::imagref_const(op1), rnd_im),
            )
        }
    };
}

macro_rules! sub_reverse {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: $T, op2: *const mpc_t, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), op1, mpc::realref_const(op2), rnd_re),
                mpfr::neg(mpc::imagref(rop), mpc::imagref_const(op2), rnd_im),
            )
        }
    };
}

macro_rules! prod_forward {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: *const mpc_t, op2: $T, rnd: rnd_t) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                $func(mpc::imagref(rop), mpc::imagref_const(op1), op2, rnd_im),
            )
        }
    };
}

macro_rules! div_reverse {
    (fn $name:ident($T:ty) -> $func:path) => {
        #[inline]
        pub unsafe fn $name(rop: *mut mpc_t, op1: $T, op2: *const mpc_t, rnd: rnd_t) -> c_int {
            let op1 = SmallComplex::from(op1);
            mpc::div(rop, op1.as_raw(), op2, rnd)
        }
    };
}

sum_forward! { fn add_ui(c_ulong) -> mpfr::add_ui }
sum_forward! { fn add_si(c_long) -> mpfr::add_si }
sum_forward! { fn add_d(f64) -> mpfr::add_d }
#[cfg(feature = "integer")]
sum_forward! { fn add_z(*const mpz_t) -> mpfr::add_z }
#[cfg(feature = "rational")]
sum_forward! { fn add_q(*const mpq_t) -> mpfr::add_q }

sum_forward! { fn sub_ui(c_ulong) -> mpfr::sub_ui }
sum_forward! { fn sub_si(c_long) -> mpfr::sub_si }
sum_forward! { fn sub_d(f64) -> mpfr::sub_d }
#[cfg(feature = "integer")]
sum_forward! { fn sub_z(*const mpz_t) -> mpfr::sub_z }
#[cfg(feature = "rational")]
sum_forward! { fn sub_q(*const mpq_t) -> mpfr::sub_q }

sub_reverse! { fn ui_sub(c_ulong) -> mpfr::ui_sub }
sub_reverse! { fn si_sub(c_long) -> mpfr::si_sub }
sub_reverse! { fn d_sub(f64) -> mpfr::d_sub }
#[cfg(feature = "integer")]
sub_reverse! { fn z_sub(*const mpz_t) -> mpfr::z_sub }
#[cfg(feature = "rational")]
sub_reverse! { fn q_sub(*const mpq_t) -> xmpfr::q_sub }

prod_forward! { fn mul_ui(c_ulong) -> mpfr::mul_ui }
prod_forward! { fn mul_si(c_long) -> mpfr::mul_si }
prod_forward! { fn mul_d(f64) -> mpfr::mul_d }
#[cfg(feature = "integer")]
prod_forward! { fn mul_z(*const mpz_t) -> mpfr::mul_z }
#[cfg(feature = "rational")]
prod_forward! { fn mul_q(*const mpq_t) -> mpfr::mul_q }

prod_forward! { fn div_ui(c_ulong) -> mpfr::div_ui }
prod_forward! { fn div_si(c_long) -> mpfr::div_si }
prod_forward! { fn div_d(f64) -> mpfr::div_d }
#[cfg(feature = "integer")]
prod_forward! { fn div_z(*const mpz_t) -> mpfr::div_z }
#[cfg(feature = "rational")]
prod_forward! { fn div_q(*const mpq_t) -> mpfr::div_q }

div_reverse! { fn ui_div(c_ulong) -> mpfr::ui_div }
div_reverse! { fn si_div(c_long) -> mpfr::si_div }
div_reverse! { fn d_div(f64) -> mpfr::d_div }

#[inline]
pub unsafe fn mulsub(
    rop: *mut mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    sub: *const mpc_t,
    rnd: rnd_t,
) -> c_int {
    let sub_complex = &*cast_ptr!(sub, Complex);
    let add = sub_complex.as_neg();
    mpc::fma(rop, m1, m2, add.as_raw(), rnd)
}

#[inline]
pub unsafe fn submul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    rnd: rnd_t,
) -> c_int {
    let m1_complex = &*cast_ptr!(m1, Complex);
    let neg_m1 = m1_complex.as_neg();
    mpc::fma(rop, neg_m1.as_raw(), m2, add, rnd)
}

#[inline]
fn rnd_re_im(r: rnd_t) -> (mpfr_rnd_t, mpfr_rnd_t) {
    let re = match r & 0x0f {
        0 => mpfr_rnd_t::RNDN,
        1 => mpfr_rnd_t::RNDZ,
        2 => mpfr_rnd_t::RNDU,
        3 => mpfr_rnd_t::RNDD,
        _ => unreachable!(),
    };
    let im = match r >> 4 {
        0 => mpfr_rnd_t::RNDN,
        1 => mpfr_rnd_t::RNDZ,
        2 => mpfr_rnd_t::RNDU,
        3 => mpfr_rnd_t::RNDD,
        _ => unreachable!(),
    };
    (re, im)
}

#[inline]
fn ord_ord(re: c_int, im: c_int) -> c_int {
    let r = match re.cmp(&0) {
        Ordering::Less => 2,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let i = match im.cmp(&0) {
        Ordering::Less => 8,
        Ordering::Equal => 0,
        Ordering::Greater => 4,
    };
    r | i
}

#[inline]
pub unsafe fn shl_u32(rop: *mut mpc_t, op1: *const mpc_t, op2: u32, rnd: rnd_t) -> c_int {
    mpc::mul_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_u32(rop: *mut mpc_t, op1: *const mpc_t, op2: u32, rnd: rnd_t) -> c_int {
    mpc::div_2ui(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shl_i32(rop: *mut mpc_t, op1: *const mpc_t, op2: i32, rnd: rnd_t) -> c_int {
    mpc::mul_2si(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn shr_i32(rop: *mut mpc_t, op1: *const mpc_t, op2: i32, rnd: rnd_t) -> c_int {
    mpc::div_2si(rop, op1, op2.into(), rnd)
}
