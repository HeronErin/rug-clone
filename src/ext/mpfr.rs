// Copyright © 2017 University of Malta

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

#[cfg(feature = "integer")]
use Float;
#[cfg(feature = "integer")]
use float;
use float::SmallFloat;
use inner::Inner;
#[cfg(feature = "integer")]
use inner::InnerMut;

#[cfg(feature = "integer")]
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
#[cfg(feature = "integer")]
use std::cmp;
use std::mem;
use std::os::raw::{c_int, c_long, c_ulong};
#[cfg(feature = "integer")]
use std::u32;

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
    let lhs_num = gmp::mpq_numref(lhs as *mut _) as *const _;
    let lhs_den = gmp::mpq_denref(lhs as *mut _) as *const _;
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
        let mut prec = (*f).prec as u32;
        assert_eq!(prec as mpfr::prec_t, (*f).prec, "overflow");
        let bits = gmp::mpz_sizeinbase(div, 2);
        assert!(bits < u32::MAX as usize, "overflow");
        prec = prec.checked_add(bits as u32).expect("overflow");
        denom_buf = Float::new(prec);
        mpfr::mul_z(denom_buf.inner_mut(), f, div, mpfr::rnd_t::RNDN);
        denom_buf.inner() as *const _
    } else {
        f
    };
    if let Some(mul) = mul {
        let bits = gmp::mpz_sizeinbase(mul, 2);
        assert!(bits <= u32::MAX as usize, "overflow");
        let mut buf = Float::new(cmp::max(float::prec_min(), bits as u32));
        mpfr::set_z(buf.inner_mut(), mul, rnd);
        mpfr::div(rop, buf.inner(), denom, rnd)
    } else {
        mpfr::ui_div(rop, 1, denom, rnd)
    }
}

#[inline]
pub unsafe fn set_f32(rop: *mut mpfr_t, op: f32, rnd: mpfr::rnd_t) -> c_int {
    mpfr::set_d(rop, op.into(), rnd)
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

#[inline]
pub unsafe fn set_i64(rop: *mut mpfr_t, val: i64, rnd: mpfr::rnd_t) -> c_int {
    if mem::size_of::<c_long>() >= 64 {
        mpfr::set_si(rop, val as c_long, rnd)
    } else {
        let small = SmallFloat::from(val);
        mpfr::set(rop, (*small).inner(), rnd)
    }
}

#[inline]
pub unsafe fn set_u64(rop: *mut mpfr_t, val: u64, rnd: mpfr::rnd_t) -> c_int {
    if mem::size_of::<c_ulong>() >= 64 {
        mpfr::set_ui(rop, val as c_ulong, rnd)
    } else {
        let small = SmallFloat::from(val);
        mpfr::set(rop, (*small).inner(), rnd)
    }
}

#[inline]
pub unsafe fn pow_f64(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f64,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::pow(rop, op1, (*small).inner(), rnd)
}

#[inline]
pub unsafe fn pow_f32(
    rop: *mut mpfr_t,
    op1: *const mpfr_t,
    op2: f32,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op2);
    mpfr::pow(rop, op1, (*small).inner(), rnd)
}

#[inline]
pub unsafe fn si_pow(
    rop: *mut mpfr_t,
    op1: c_long,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).inner(), op2, rnd)
}

#[inline]
pub unsafe fn f32_pow(
    rop: *mut mpfr_t,
    op1: f32,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).inner(), op2, rnd)
}

#[inline]
pub unsafe fn f64_pow(
    rop: *mut mpfr_t,
    op1: f64,
    op2: *const mpfr_t,
    rnd: mpfr::rnd_t,
) -> c_int {
    let small = SmallFloat::from(op1);
    mpfr::pow(rop, (*small).inner(), op2, rnd)
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
    if mpfr::nan_p(rop) == 0 {
        (*rop).sign = -(*rop).sign;
    }
    -reverse_ord
}
