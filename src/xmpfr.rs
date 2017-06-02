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

use float::{Float, prec_min};
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpfr::{self, mpfr_t};
use std::cmp;
use std::os::raw::c_int;
use std::u32;

pub unsafe fn recip(rop: *mut mpfr_t,
                    op: *const mpfr_t,
                    rnd: mpfr::rnd_t)
                    -> c_int {
    mpfr::ui_div(rop, 1, op, rnd)
}

pub unsafe fn jn(rop: *mut mpfr_t,
                 op: *const mpfr_t,
                 n: i32,
                 rnd: mpfr::rnd_t)
                 -> c_int {
    mpfr::jn(rop, n.into(), op, rnd)
}

pub unsafe fn yn(rop: *mut mpfr_t,
                 op: *const mpfr_t,
                 n: i32,
                 rnd: mpfr::rnd_t)
                 -> c_int {
    mpfr::yn(rop, n.into(), op, rnd)
}

pub unsafe fn z_div(r: *mut mpfr_t,
                    lhs: *const gmp::mpz_t,
                    rhs: *const mpfr_t,
                    rnd: mpfr::rnd_t)
                    -> c_int {
    divf_mulz_divz(r, rhs, Some(lhs), None, rnd)
}

pub unsafe fn q_sub(r: *mut mpfr_t,
                    lhs: *const gmp::mpq_t,
                    rhs: *const mpfr_t,
                    rnd: mpfr::rnd_t)
                    -> c_int {
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

pub unsafe fn q_div(r: *mut mpfr_t,
                    lhs: *const gmp::mpq_t,
                    rhs: *const mpfr_t,
                    rnd: mpfr::rnd_t)
                    -> c_int {
    let lhs_num = gmp::mpq_numref(lhs as *mut _) as *const _;
    let lhs_den = gmp::mpq_denref(lhs as *mut _) as *const _;
    divf_mulz_divz(r, rhs, Some(lhs_num), Some(lhs_den), rnd)
}

// mul and div must must form a canonical rational, except that div
// can be negative
unsafe fn divf_mulz_divz(rop: *mut mpfr_t,
                         f: *const mpfr_t,
                         mul: Option<*const gmp::mpz_t>,
                         div: Option<*const gmp::mpz_t>,
                         rnd: mpfr::rnd_t)
                         -> c_int {
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
        let mut buf = Float::new(cmp::max(prec_min(), bits as u32));
        mpfr::set_z(buf.inner_mut(), mul, rnd);
        mpfr::div(rop, buf.inner(), denom, rnd)
    } else {
        mpfr::ui_div(rop, 1, denom, rnd)
    }
}

pub unsafe fn set_single(rop: *mut mpfr_t, op: f32, rnd: mpfr::rnd_t) -> c_int {
    mpfr::set_d(rop, op as f64, rnd)
}

pub unsafe fn add_single(rop: *mut mpfr_t,
                         op1: *const mpfr_t,
                         op2: f32,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::add_d(rop, op1, op2 as f64, rnd)
}

pub unsafe fn sub_single(rop: *mut mpfr_t,
                         op1: *const mpfr_t,
                         op2: f32,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::sub_d(rop, op1, op2 as f64, rnd)
}

pub unsafe fn single_sub(rop: *mut mpfr_t,
                         op1: f32,
                         op2: *const mpfr_t,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::d_sub(rop, op1 as f64, op2, rnd)
}

pub unsafe fn mul_single(rop: *mut mpfr_t,
                         op1: *const mpfr_t,
                         op2: f32,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::mul_d(rop, op1, op2 as f64, rnd)
}

pub unsafe fn div_single(rop: *mut mpfr_t,
                         op1: *const mpfr_t,
                         op2: f32,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::div_d(rop, op1, op2 as f64, rnd)
}

pub unsafe fn single_div(rop: *mut mpfr_t,
                         op1: f32,
                         op2: *const mpfr_t,
                         rnd: mpfr::rnd_t)
                         -> c_int {
    mpfr::d_div(rop, op1 as f64, op2, rnd)
}

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Float {
    type Output = mpfr_t;
    fn inner(&self) -> &mpfr_t {
        let ptr = self as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl InnerMut for Float {
    unsafe fn inner_mut(&mut self) -> &mut mpfr_t {
        let ptr = self as *mut _ as *mut _;
        &mut *ptr
    }
}
