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

use Complex;
use complex::SmallComplex;
#[cfg(feature = "rational")]
use ext::mpfr as xmpfr;
#[cfg(feature = "integer")]
use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpc::{self, mpc_t};
use gmp_mpfr_sys::mpfr;
use inner::Inner;
use std::cmp::Ordering;
use std::os::raw::{c_int, c_long, c_ulong};

#[inline]
pub unsafe fn mul_i(
    rop: *mut mpc_t,
    op: *const mpc_t,
    neg: bool,
    rnd: mpc::rnd_t,
) -> c_int {
    mpc::mul_i(rop, op, if neg { -1 } else { 0 }, rnd)
}

#[inline]
pub unsafe fn recip(
    rop: *mut mpc_t,
    op: *const mpc_t,
    rnd: mpc::rnd_t,
) -> c_int {
    ui_div(rop, 1, op, rnd)
}

macro_rules! into_forward {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: *const mpc_t,
            op2: $T,
            rnd: mpc::rnd_t,
        ) -> c_int {
            $func(rop, op1, op2.into(), rnd)
        }
    };
}

macro_rules! into_reverse {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: $T,
            op2: *const mpc_t,
            rnd: mpc::rnd_t,
        ) -> c_int {
            $func(rop, op1.into(), op2, rnd)
        }
    };
}

macro_rules! sum_forward {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: *const mpc_t,
            op2: $T,
            rnd: mpc::rnd_t,
        ) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                mpfr::set(mpc::imagref(rop), mpc::imagref_const(op1), rnd_im),
            )
        }
    };
}

macro_rules! sub_reverse {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: $T,
            op2: *const mpc_t,
            rnd: mpc::rnd_t,
        ) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), op1, mpc::realref_const(op2), rnd_re),
                mpfr::neg(mpc::imagref(rop), mpc::imagref_const(op2), rnd_im),
            )
        }
    };
}

macro_rules! prod_forward {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: *const mpc_t,
            op2: $T,
            rnd: mpc::rnd_t,
        ) -> c_int {
            let (rnd_re, rnd_im) = rnd_re_im(rnd);
            ord_ord(
                $func(mpc::realref(rop), mpc::realref_const(op1), op2, rnd_re),
                $func(mpc::imagref(rop), mpc::imagref_const(op1), op2, rnd_im),
            )
        }
    };
}

macro_rules! div_reverse {
    (fn $name: ident($T: ty) -> $func: path) => {
        #[inline]
        pub unsafe fn $name(
            rop: *mut mpc_t,
            op1: $T,
            op2: *const mpc_t,
            rnd: mpc::rnd_t,
        ) -> c_int {
            let op1 = SmallComplex::from(op1);
            mpc::div(rop, op1.inner(), op2, rnd)
        }
    };
}

sum_forward! { fn add_ui(c_ulong) -> mpfr::add_ui }
sum_forward! { fn add_si(c_long) -> mpfr::add_si }
into_forward! { fn add_f32(f32) -> add_f64 }
sum_forward! { fn add_f64(f64) -> mpfr::add_d }
#[cfg(feature = "integer")]
sum_forward! { fn add_z(*const gmp::mpz_t) -> mpfr::add_z }
#[cfg(feature = "rational")]
sum_forward! { fn add_q(*const gmp::mpq_t) -> mpfr::add_q }

sum_forward! { fn sub_ui(c_ulong) -> mpfr::sub_ui }
sum_forward! { fn sub_si(c_long) -> mpfr::sub_si }
into_forward! { fn sub_f32(f32) -> sub_f64 }
sum_forward! { fn sub_f64(f64) -> mpfr::sub_d }
#[cfg(feature = "integer")]
sum_forward! { fn sub_z(*const gmp::mpz_t) -> mpfr::sub_z }
#[cfg(feature = "rational")]
sum_forward! { fn sub_q(*const gmp::mpq_t) -> mpfr::sub_q }

sub_reverse! { fn ui_sub(c_ulong) -> mpfr::ui_sub }
sub_reverse! { fn si_sub(c_long) -> mpfr::si_sub }
into_reverse! { fn f32_sub(f32) -> f64_sub }
sub_reverse! { fn f64_sub(f64) -> mpfr::d_sub }
#[cfg(feature = "integer")]
sub_reverse! { fn z_sub(*const gmp::mpz_t) -> mpfr::z_sub }
#[cfg(feature = "rational")]
sub_reverse! { fn q_sub(*const gmp::mpq_t) -> xmpfr::q_sub }

prod_forward! { fn mul_ui(c_ulong) -> mpfr::mul_ui }
prod_forward! { fn mul_si(c_long) -> mpfr::mul_si }
into_forward! { fn mul_f32(f32) -> mul_f64 }
prod_forward! { fn mul_f64(f64) -> mpfr::mul_d }
#[cfg(feature = "integer")]
prod_forward! { fn mul_z(*const gmp::mpz_t) -> mpfr::mul_z }
#[cfg(feature = "rational")]
prod_forward! { fn mul_q(*const gmp::mpq_t) -> mpfr::mul_q }

prod_forward! { fn div_ui(c_ulong) -> mpfr::div_ui }
prod_forward! { fn div_si(c_long) -> mpfr::div_si }
into_forward! { fn div_f32(f32) -> div_f64 }
prod_forward! { fn div_f64(f64) -> mpfr::div_d }
#[cfg(feature = "integer")]
prod_forward! { fn div_z(*const gmp::mpz_t) -> mpfr::div_z }
#[cfg(feature = "rational")]
prod_forward! { fn div_q(*const gmp::mpq_t) -> mpfr::div_q }

div_reverse! { fn ui_div(c_ulong) -> mpfr::ui_div }
div_reverse! { fn si_div(c_long) -> mpfr::si_div }
into_reverse! { fn f32_div(f32) -> f64_div }
div_reverse! { fn f64_div(f64) -> mpfr::d_div }

into_forward! { fn pow_f32(f32) -> mpc::pow_d }

#[inline]
pub unsafe fn mulsub(
    rop: *mut mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    sub: *const mpc_t,
    rnd: mpc::rnd_t,
) -> c_int {
    let sub_complex = &*(sub as *const Complex);
    let add = sub_complex.as_neg();
    mpc::fma(rop, m1, m2, add.inner(), rnd)
}

#[inline]
pub unsafe fn submul(
    rop: *mut mpc_t,
    add: *const mpc_t,
    (m1, m2): (*const mpc_t, *const mpc_t),
    rnd: mpc::rnd_t,
) -> c_int {
    let m1_complex = &*(m1 as *const Complex);
    let neg_m1 = m1_complex.as_neg();
    mpc::fma(rop, neg_m1.inner(), m2, add, rnd)
}

#[inline]
fn rnd_re_im(r: mpc::rnd_t) -> (mpfr::rnd_t, mpfr::rnd_t) {
    let re = match r & 0x0f {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
        _ => unreachable!(),
    };
    let im = match r >> 4 {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
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
