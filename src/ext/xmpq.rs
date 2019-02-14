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

use cast;
use ext::xmpz;
use gmp_mpfr_sys::gmp::{self, mpq_t, mpz_t};
use misc::NegAbs;
use rational::SmallRational;
use std::mem;
use std::os::raw::c_int;
use {Integer, Rational};

macro_rules! wrap {
    (fn $fn:ident($($op:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Rational,
            $($op: Option<&Rational>,)*
            $($param: $T,)*
        ) {
            unsafe {
                $deleg(
                    rop.as_raw_mut(),
                    $($op.unwrap_or(rop).as_raw(),)*
                    $($param.into(),)*
                );
            }
        }
    };
}

#[inline]
pub fn set(rop: &mut Rational, op: Option<&Rational>) {
    if let Some(op) = op {
        unsafe {
            gmp::mpq_set(rop.as_raw_mut(), op.as_raw());
        }
    }
}

#[inline]
pub fn signum(num: &mut Integer, den: Option<&Integer>, op: Option<&Rational>) {
    let _ = den;
    xmpz::signum(num, op.map(Rational::numer));
}

#[inline]
pub fn trunc(num: &mut Integer, den: Option<&Integer>, op: Option<&Rational>) {
    let (op_num, op_den) = match (den, op) {
        (None, Some(rat)) => (rat.numer().as_raw(), rat.denom().as_raw()),
        (Some(den), None) => (num.as_raw(), den.as_raw()),
        _ => unreachable!(),
    };
    unsafe {
        gmp::mpz_tdiv_q(num.as_raw_mut(), op_num, op_den);
    }
}

#[inline]
pub fn ceil(num: &mut Integer, den: Option<&Integer>, op: Option<&Rational>) {
    let (op_num, op_den) = match (den, op) {
        (None, Some(rat)) => (rat.numer().as_raw(), rat.denom().as_raw()),
        (Some(den), None) => (num.as_raw(), den.as_raw()),
        _ => unreachable!(),
    };
    unsafe {
        if gmp::mpz_cmp_ui(op_den, 1) == 0 {
            gmp::mpz_set(num.as_raw_mut(), op_num);
        } else {
            // use tdiv_q rather than cdiv_q to let GMP not keep remainder
            let neg = gmp::mpz_sgn(op_num) < 0;
            gmp::mpz_tdiv_q(num.as_raw_mut(), op_num, op_den);
            if !neg {
                gmp::mpz_add_ui(num.as_raw_mut(), num.as_raw(), 1);
            }
        }
    }
}

#[inline]
pub fn floor(num: &mut Integer, den: Option<&Integer>, op: Option<&Rational>) {
    let (op_num, op_den) = match (den, op) {
        (None, Some(rat)) => (rat.numer().as_raw(), rat.denom().as_raw()),
        (Some(den), None) => (num.as_raw(), den.as_raw()),
        _ => unreachable!(),
    };
    unsafe {
        if gmp::mpz_cmp_ui(op_den, 1) == 0 {
            gmp::mpz_set(num.as_raw_mut(), op_num);
        } else {
            // use tdiv_q rather than fdiv_q to let GMP not keep remainder
            let neg = gmp::mpz_sgn(op_num) < 0;
            gmp::mpz_tdiv_q(num.as_raw_mut(), op_num, op_den);
            if neg {
                gmp::mpz_sub_ui(num.as_raw_mut(), num.as_raw(), 1);
            }
        }
    }
}

pub fn round(num: &mut Integer, den: Option<&Integer>, op: Option<&Rational>) {
    let (op_num, op_den) = match (den, op) {
        (None, Some(rat)) => (rat.numer().as_raw(), rat.denom().as_raw()),
        (Some(den), None) => (num.as_raw(), den.as_raw()),
        _ => unreachable!(),
    };

    unsafe {
        if gmp::mpz_cmp_ui(op_den, 1) == 0 {
            gmp::mpz_set(num.as_raw_mut(), op_num);
            return;
        }
        // The remainder cannot be larger than the divisor, but we
        // allocate an extra limb because the GMP docs suggest we should.
        let limbs = cast::cast::<_, gmp::bitcnt_t>((*op_den).size.abs()) + 1;
        let bits = limbs
            .checked_mul(cast::cast::<_, gmp::bitcnt_t>(gmp::LIMB_BITS))
            .expect("overflow");
        let mut rem: mpz_t = mem::uninitialized();
        gmp::mpz_init2(&mut rem, bits);
        gmp::mpz_tdiv_qr(num.as_raw_mut(), &mut rem, op_num, op_den);
        if xmpz::round_away(&rem, op_den) {
            if gmp::mpz_sgn(&rem) >= 0 {
                // positive number
                gmp::mpz_add_ui(num.as_raw_mut(), num.as_raw(), 1);
            } else {
                // negative number
                gmp::mpz_sub_ui(num.as_raw_mut(), num.as_raw(), 1);
            }
        }
        gmp::mpz_clear(&mut rem);
    }
}

#[inline]
pub fn inv(rop: &mut Rational, op: Option<&Rational>) {
    let op_ptr = op.unwrap_or(rop).as_raw();
    unsafe {
        assert_ne!(gmp::mpq_sgn(op_ptr), 0, "division by zero");
        gmp::mpq_inv(rop.as_raw_mut(), op_ptr);
    }
}

#[inline]
pub fn trunc_fract(fract: &mut Rational, op: Option<&Rational>) {
    let fract_ptr = fract.as_raw_mut();
    let op_ptr = op.unwrap_or(fract).as_raw();
    unsafe {
        let fract_num = gmp::mpq_numref(fract_ptr);
        let fract_den = gmp::mpq_denref(fract_ptr);
        let num = gmp::mpq_numref_const(op_ptr);
        let den = gmp::mpq_denref_const(op_ptr);
        gmp::mpz_tdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }
}

#[inline]
pub fn ceil_fract(fract: &mut Rational, op: Option<&Rational>) {
    let fract_ptr = fract.as_raw_mut();
    let op_ptr = op.unwrap_or(fract).as_raw();
    unsafe {
        let fract_num = gmp::mpq_numref(fract_ptr);
        let fract_den = gmp::mpq_denref(fract_ptr);
        let num = gmp::mpq_numref_const(op_ptr);
        let den = gmp::mpq_denref_const(op_ptr);
        gmp::mpz_cdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }
}

#[inline]
pub fn floor_fract(fract: &mut Rational, op: Option<&Rational>) {
    let fract_ptr = fract.as_raw_mut();
    let op_ptr = op.unwrap_or(fract).as_raw();
    unsafe {
        let fract_num = gmp::mpq_numref(fract_ptr);
        let fract_den = gmp::mpq_denref(fract_ptr);
        let num = gmp::mpq_numref_const(op_ptr);
        let den = gmp::mpq_denref_const(op_ptr);
        gmp::mpz_fdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }
}

pub fn round_fract(fract: &mut Rational, op: Option<&Rational>) {
    let fract_ptr = fract.as_raw_mut();
    let op_ptr = op.unwrap_or(fract).as_raw();
    unsafe {
        let fract_num = gmp::mpq_numref(fract_ptr);
        let fract_den = gmp::mpq_denref(fract_ptr);
        let num = gmp::mpq_numref_const(op_ptr);
        let den = gmp::mpq_denref_const(op_ptr);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            xmpz::mpz_set_0(fract_num);
            xmpz::mpz_set_1(fract_den);
            return;
        }
        gmp::mpz_tdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
        if xmpz::round_away(fract_num, fract_den) {
            if gmp::mpz_sgn(fract_num) >= 0 {
                // positive number
                gmp::mpz_sub(fract_num, fract_num, fract_den);
            } else {
                // negative number
                gmp::mpz_add(fract_num, fract_num, fract_den);
            }
        }
    }
}

#[inline]
pub fn square(rop: &mut Rational, op: Option<&Rational>) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op_num = op.map(Rational::numer);
        let op_den = op.map(Rational::denom);
        xmpz::square(rop_num, op_num);
        xmpz::square(rop_den, op_den);
    }
}

wrap! { fn neg(op) -> gmp::mpq_neg }
wrap! { fn abs(op) -> gmp::mpq_abs }
wrap! { fn add(op1, op2) -> gmp::mpq_add }
wrap! { fn sub(op1, op2) -> gmp::mpq_sub }
wrap! { fn mul(op1, op2) -> gmp::mpq_mul }
wrap! { fn div(op1, op2) -> gmp::mpq_div }
wrap! { fn mul_2exp(op1; op2: u32) -> gmp::mpq_mul_2exp }
wrap! { fn div_2exp(op1; op2: u32) -> gmp::mpq_div_2exp }

#[inline]
pub fn lshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        mul_2exp(rop, op1, op2_abs);
    } else {
        div_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn rshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        div_2exp(rop, op1, op2_abs);
    } else {
        mul_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn pow_u32(rop: &mut Rational, op1: Option<&Rational>, op2: u32) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op1_num = op1.map(Rational::numer);
        let op1_den = op1.map(Rational::denom);
        xmpz::pow_u32(rop_num, op1_num, op2);
        xmpz::pow_u32(rop_den, op1_den, op2);
    }
}

#[inline]
pub fn pow_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    pow_u32(rop, op1, op2_abs);
    if !op2_neg {
        inv(rop, None);
    }
}

#[inline]
pub unsafe fn mpq_trunc_fract_whole(
    fract: *mut mpq_t,
    trunc: *mut mpz_t,
    op: *const mpq_t,
) {
    let fract_num = gmp::mpq_numref(fract);
    let fract_den = gmp::mpq_denref(fract);
    let num = gmp::mpq_numref_const(op);
    let den = gmp::mpq_denref_const(op);
    gmp::mpz_tdiv_qr(trunc, fract_num, num, den);
    gmp::mpz_set(fract_den, den);
}

#[inline]
pub unsafe fn mpq_ceil_fract_whole(
    fract: *mut mpq_t,
    ceil: *mut mpz_t,
    op: *const mpq_t,
) {
    let fract_num = gmp::mpq_numref(fract);
    let fract_den = gmp::mpq_denref(fract);
    let num = gmp::mpq_numref_const(op);
    let den = gmp::mpq_denref_const(op);
    gmp::mpz_cdiv_qr(ceil, fract_num, num, den);
    gmp::mpz_set(fract_den, den);
}

#[inline]
pub unsafe fn mpq_floor_fract_whole(
    fract: *mut mpq_t,
    floor: *mut mpz_t,
    op: *const mpq_t,
) {
    let fract_num = gmp::mpq_numref(fract);
    let fract_den = gmp::mpq_denref(fract);
    let num = gmp::mpq_numref_const(op);
    let den = gmp::mpq_denref_const(op);
    gmp::mpz_fdiv_qr(floor, fract_num, num, den);
    gmp::mpz_set(fract_den, den);
}

pub unsafe fn mpq_round_fract_whole(
    fract: *mut mpq_t,
    round: *mut mpz_t,
    op: *const mpq_t,
) {
    let fract_num = gmp::mpq_numref(fract);
    let fract_den = gmp::mpq_denref(fract);
    let num = gmp::mpq_numref_const(op);
    let den = gmp::mpq_denref_const(op);
    if gmp::mpz_cmp_ui(den, 1) == 0 {
        // set round before fract_num, which might alias num
        gmp::mpz_set(round, num);
        xmpz::mpz_set_0(fract_num);
        xmpz::mpz_set_1(fract_den);
        return;
    }
    gmp::mpz_tdiv_qr(round, fract_num, num, den);
    gmp::mpz_set(fract_den, den);
    if xmpz::round_away(fract_num, fract_den) {
        if gmp::mpz_sgn(fract_num) >= 0 {
            // positive number
            gmp::mpz_sub(fract_num, fract_num, fract_den);
            gmp::mpz_add_ui(round, round, 1);
        } else {
            // negative number
            gmp::mpz_add(fract_num, fract_num, fract_den);
            gmp::mpz_sub_ui(round, round, 1);
        }
    }
}

#[inline]
pub unsafe fn mpq_cmp_u64(op1: *const mpq_t, n2: u64, d2: u64) -> c_int {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return gmp::mpq_cmp_ui(op1, n2, d2);
        }
    }
    let small = SmallRational::from((n2, d2));
    gmp::mpq_cmp(op1, (*small).as_raw())
}

#[inline]
pub unsafe fn mpq_cmp_i64(op1: *const mpq_t, n2: i64, d2: u64) -> c_int {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return gmp::mpq_cmp_si(op1, n2, d2);
        }
    }
    let small = SmallRational::from((n2, d2));
    gmp::mpq_cmp(op1, (*small).as_raw())
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpq_cmp_u128(op1: *const mpq_t, n2: u128, d2: u128) -> c_int {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return gmp::mpq_cmp_ui(op1, n2, d2);
        }
    }
    let small = SmallRational::from((n2, d2));
    gmp::mpq_cmp(op1, (*small).as_raw())
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpq_cmp_i128(op1: *const mpq_t, n2: i128, d2: u128) -> c_int {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return gmp::mpq_cmp_si(op1, n2, d2);
        }
    }
    let small = SmallRational::from((n2, d2));
    gmp::mpq_cmp(op1, (*small).as_raw())
}

pub unsafe fn mpq_cmp_finite_d(op1: *const mpq_t, op2: f64) -> c_int {
    let num1 = gmp::mpq_numref_const(op1);
    let den1 = gmp::mpq_denref_const(op1);
    let den1_bits = gmp::mpz_sizeinbase(den1, 2);
    // cmp(num1, op2 * den1)
    let mut op2_f = mem::uninitialized();
    let mut rhs = mem::uninitialized();
    gmp::mpf_init2(&mut op2_f, 53);
    gmp::mpf_set_d(&mut op2_f, op2);
    gmp::mpf_init2(&mut rhs, cast::cast(den1_bits + 53));
    gmp::mpf_set_z(&mut rhs, den1);
    gmp::mpf_mul(&mut rhs, &rhs, &op2_f);
    let ret = -gmp::mpf_cmp_z(&rhs, num1);
    gmp::mpf_clear(&mut rhs);
    gmp::mpf_clear(&mut op2_f);
    ret
}
