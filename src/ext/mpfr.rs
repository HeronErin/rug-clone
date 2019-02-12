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

use cast::cast;
#[cfg(feature = "integer")]
use float;
use float::SmallFloat;
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
#[cfg(feature = "integer")]
use misc::NegAbs;
#[cfg(feature = "integer")]
use std::cmp;
use std::mem;
use std::os::raw::{c_int, c_long, c_ulong, c_void};
#[cfg(feature = "integer")]
use std::u32;
#[cfg(feature = "integer")]
use Float;

#[inline]
pub unsafe fn signum(
    rop: *mut mpfr_t,
    op: *const mpfr_t,
    _rnd: mpfr::rnd_t,
) -> c_int {
    if mpfr::nan_p(op) != 0 {
        mpfr::set(rop, op, mpfr::rnd_t::RNDZ)
    } else if mpfr::signbit(op) != 0 {
        mpfr::set_si(rop, -1, mpfr::rnd_t::RNDZ)
    } else {
        mpfr::set_si(rop, 1, mpfr::rnd_t::RNDZ)
    }
}

#[inline]
pub unsafe fn recip(
    rop: *mut mpfr_t,
    op: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::ui_div(rop, 1, op, rnd)
}

#[inline]
pub unsafe fn jn(
    rop: *mut mpfr_t,
    op: *const mpfr_t,
    n: i32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::jn(rop, n.into(), op, rnd)
}

#[inline]
pub unsafe fn yn(
    rop: *mut mpfr_t,
    op: *const mpfr_t,
    n: i32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::yn(rop, n.into(), op, rnd)
}

#[cfg(feature = "integer")]
#[inline]
pub unsafe fn z_div(
    r: *mut mpfr_t,
    lhs: *const gmp::mpz_t,
    rhs: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    divf_mulz_divz(r, rhs, Some(lhs), None, rnd)
}

#[cfg(feature = "rational")]
#[inline]
pub unsafe fn q_sub(
    r: *mut mpfr_t,
    lhs: *const gmp::mpq_t,
    rhs: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let flip_rnd = match rnd {
        mpfr::rnd_t::RNDU => mpfr::rnd_t::RNDD,
        mpfr::rnd_t::RNDD => mpfr::rnd_t::RNDU,
        unchanged => unchanged,
    };
    let flip_ret = -mpfr::sub_q(r, rhs, lhs, flip_rnd);
    if mpfr::zero_p(r) == 0 {
        // the negation here is exact
        mpfr::neg(r, r, mpfr::rnd_t::RNDN);
    }
    -flip_ret
}

#[cfg(feature = "rational")]
#[inline]
pub unsafe fn q_div(
    r: *mut mpfr_t,
    lhs: *const gmp::mpq_t,
    rhs: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
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
    mul: Option<*const gmp::mpz_t>,
    div: Option<*const gmp::mpz_t>,
    rnd: mpfr::rnd_t,
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
        let mut prec: u32 = cast((*f).prec);
        let bits: u32 = cast(gmp::mpz_sizeinbase(div, 2));
        prec = prec.checked_add(bits).expect("overflow");
        denom_buf = Float::new(prec);
        mpfr::mul_z(denom_buf.as_raw_mut(), f, div, mpfr::rnd_t::RNDN);
        denom_buf.as_raw()
    } else {
        f
    };
    if let Some(mul) = mul {
        let bits: u32 = cast(gmp::mpz_sizeinbase(mul, 2));
        let mut buf = Float::new(cmp::max(float::prec_min(), bits));
        mpfr::set_z(buf.as_raw_mut(), mul, rnd);
        mpfr::div(rop, buf.as_raw(), denom, rnd)
    } else {
        mpfr::ui_div(rop, 1, denom, rnd)
    }
}

pub unsafe fn get_f32(op: *const mpfr_t, rnd: mpfr::rnd_t) -> f32 {
    let mut single: mpfr_t = mem::uninitialized();
    let mut limb: gmp::limb_t = 0;
    custom_zero(&mut single, &mut limb, 24);
    mpfr::set(&mut single, op, rnd);
    let val = mpfr::get_d(&single, rnd);
    val as f32
}

#[inline]
pub unsafe fn set_f32(rop: *mut mpfr_t, op: f32, rnd: mpfr::rnd_t) -> c_int {
    set_f64(rop, op.into(), rnd)
}

#[inline]
pub unsafe fn set_f64(rop: *mut mpfr_t, op: f64, rnd: mpfr::rnd_t) -> c_int {
    // retain sign in case of NaN
    let sign_neg = op.is_sign_negative();
    let ret = mpfr::set_d(rop, op, rnd);
    if sign_neg {
        (*rop).sign = -1;
    }
    ret
}

#[inline]
pub unsafe fn add_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::add_d(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn sub_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::sub_d(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn f32_sub(
    rop: *mut mpfr_t,
    op1: f32,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::d_sub(rop, op1.into(), op2, rnd)
}

#[inline]
pub unsafe fn mul_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::mul_d(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn div_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::div_d(rop, op1, op2.into(), rnd)
}

#[inline]
pub unsafe fn f32_div(
    rop: *mut mpfr_t,
    op1: f32,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    mpfr::d_div(rop, op1.into(), op2, rnd)
}

#[cfg(int_128)]
#[inline]
pub unsafe fn set_i128(rop: *mut mpfr_t, val: i128, rnd: mpfr::rnd_t) -> c_int {
    let small = SmallFloat::from(val);
    mpfr::set(rop, (*small).as_raw(), rnd)
}

#[cfg(int_128)]
#[inline]
pub unsafe fn set_u128(rop: *mut mpfr_t, val: u128, rnd: mpfr::rnd_t) -> c_int {
    let small = SmallFloat::from(val);
    mpfr::set(rop, (*small).as_raw(), rnd)
}

#[inline]
pub unsafe fn cmp_i64(op1: *const mpfr_t, op2: i64) -> c_int {
    if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
        mpfr::cmp_si(op1, cast(op2))
    } else {
        let small = SmallFloat::from(op2);
        mpfr::cmp(op1, (*small).as_raw())
    }
}

#[inline]
pub unsafe fn cmp_u64(op1: *const mpfr_t, op2: u64) -> c_int {
    if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
        mpfr::cmp_ui(op1, cast(op2))
    } else {
        let small = SmallFloat::from(op2);
        mpfr::cmp(op1, (*small).as_raw())
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn cmp_i128(op1: *const mpfr_t, op2: i128) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::cmp(op1, (*small).as_raw())
}

#[cfg(int_128)]
#[inline]
pub unsafe fn cmp_u128(op1: *const mpfr_t, op2: u128) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::cmp(op1, (*small).as_raw())
}

#[inline]
pub unsafe fn pow_f64(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f64,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::pow(rop, op1, (*small).as_raw(), rnd)
}

#[inline]
pub unsafe fn pow_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::pow(rop, op1, (*small).as_raw(), rnd)
}

#[inline]
pub unsafe fn si_pow(
    rop: *mut mpfr_t,
    op1: c_long,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).as_raw(), op2, rnd)
}

#[inline]
pub unsafe fn si_pow_ui(
    rop: *mut mpfr_t,
    op1: c_long,
    op2: c_ulong,
    rnd: mpfr::rnd_t,
) -> c_int {
    let (op1_neg, op1_abs) = op1.neg_abs();
    if !op1_neg || (op2 & 1) == 0 {
        mpfr::ui_pow_ui(rop, op1_abs, op2, rnd)
    } else {
        let reverse_rnd = match rnd {
            mpfr::rnd_t::RNDU => mpfr::rnd_t::RNDD,
            mpfr::rnd_t::RNDD => mpfr::rnd_t::RNDU,
            unchanged => unchanged,
        };
        let reverse_ord = mpfr::ui_pow_ui(rop, op1_abs, op2, reverse_rnd);
        (*rop).sign = -(*rop).sign;
        -reverse_ord
    }
}

#[inline]
pub unsafe fn f32_pow(
    rop: *mut mpfr_t,
    op1: f32,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).as_raw(), op2, rnd)
}

#[inline]
pub unsafe fn f64_pow(
    rop: *mut mpfr_t,
    op1: f64,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).as_raw(), op2, rnd)
}

#[inline]
pub unsafe fn submul(
    rop: *mut mpfr_t,
    add: *const mpfr_t,
    (m1, m2): (*const mpfr_t, *const mpfr_t),
    rnd: mpfr::rnd_t,
) -> c_int {
    let reverse_rnd = match rnd {
        mpfr::rnd_t::RNDU => mpfr::rnd_t::RNDD,
        mpfr::rnd_t::RNDD => mpfr::rnd_t::RNDU,
        unchanged => unchanged,
    };
    let reverse_ord = mpfr::fms(rop, m1, m2, add, reverse_rnd);
    (*rop).sign = -(*rop).sign;
    -reverse_ord
}

#[inline]
pub unsafe fn custom_zero(
    f: *mut mpfr_t,
    limbs: *mut gmp::limb_t,
    prec: mpfr::prec_t,
) {
    mpfr::custom_init(limbs as *mut c_void, prec);
    mpfr::custom_init_set(f, mpfr::ZERO_KIND, 0, prec, limbs as *mut c_void);
}

#[inline]
pub unsafe fn custom_regular(
    f: *mut mpfr_t,
    limbs: *mut gmp::limb_t,
    exp: mpfr::exp_t,
    prec: mpfr::prec_t,
) {
    mpfr::custom_init(limbs as *mut c_void, prec);
    mpfr::custom_init_set(
        f,
        mpfr::REGULAR_KIND,
        exp,
        prec,
        limbs as *mut c_void,
    );
}
