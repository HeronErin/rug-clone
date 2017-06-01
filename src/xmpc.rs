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

use complex::{Complex, SmallComplex};
use gmp_mpfr_sys::mpc::{self, mpc_t};
use gmp_mpfr_sys::mpfr;
use std::cmp::Ordering;
use std::os::raw::{c_int, c_long, c_ulong};

pub unsafe fn mul_i(rop: *mut mpc_t,
                    op: *const mpc_t,
                    neg: bool,
                    rnd: mpc::rnd_t)
                    -> c_int {
    mpc::mul_i(rop, op, if neg { -1 } else { 0 }, rnd)
}

pub unsafe fn recip(rop: *mut mpc_t,
                    op: *const mpc_t,
                    rnd: mpc::rnd_t)
                    -> c_int {
    ui_div(rop, 1, op, rnd)
}

pub unsafe fn ui_sub(x: *mut mpc_t,
                     y: c_ulong,
                     z: *const mpc_t,
                     r: mpc::rnd_t)
                     -> c_int {
    let mz = z as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    ord_ord(mpfr::ui_sub(mpc::realref(x), y, mpc::realref(mz), r_re),
            mpfr::neg(mpc::imagref(x), mpc::imagref(mz), r_im))
}

pub unsafe fn add_si(x: *mut mpc_t,
                     y: *const mpc_t,
                     z: c_long,
                     r: mpc::rnd_t)
                     -> c_int {
    if z < 0 {
        mpc::sub_ui(x, y, z.wrapping_neg() as c_ulong, r)
    } else {
        mpc::add_ui(x, y, z as c_ulong, r)
    }
}

pub unsafe fn sub_si(x: *mut mpc_t,
                     y: *const mpc_t,
                     z: c_long,
                     r: mpc::rnd_t)
                     -> c_int {
    if z < 0 {
        mpc::add_ui(x, y, z.wrapping_neg() as c_ulong, r)
    } else {
        mpc::sub_ui(x, y, z as c_ulong, r)
    }
}

pub unsafe fn si_sub(x: *mut mpc_t,
                     y: c_long,
                     z: *const mpc_t,
                     r: mpc::rnd_t)
                     -> c_int {
    let mz = z as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    ord_ord(mpfr::si_sub(mpc::realref(x), y, mpc::realref(mz), r_re),
            mpfr::neg(mpc::imagref(x), mpc::imagref(mz), r_im))
}

pub unsafe fn div_si(x: *mut mpc_t,
                     y: *const mpc_t,
                     z: c_long,
                     r: mpc::rnd_t)
                     -> c_int {
    let my = y as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    ord_ord(mpfr::div_si(mpc::realref(x), mpc::realref(my), z, r_re),
            mpfr::div_si(mpc::imagref(x), mpc::imagref(my), z, r_im))
}

pub unsafe fn si_div(x: *mut mpc_t,
                     y: c_long,
                     z: *const mpc_t,
                     r: mpc::rnd_t)
                     -> c_int {
    let dividend = SmallComplex::from(y);
    mpc::div(x, dividend.inner(), z, r)
}

pub unsafe fn ui_div(x: *mut mpc_t,
                     y: c_ulong,
                     z: *const mpc_t,
                     r: mpc::rnd_t)
                     -> c_int {
    let dividend = SmallComplex::from(y);
    mpc::div(x, dividend.inner(), z, r)
}

pub unsafe fn pow_single(x: *mut mpc_t,
                         y: *const mpc_t,
                         z: f32,
                         r: mpc::rnd_t)
                         -> c_int {
    mpc::pow_d(x, y, z as f64, r)
}

fn rnd_re_im(r: mpc::rnd_t) -> (mpfr::rnd_t, mpfr::rnd_t) {
    let re = match r & 0x0f {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
        4 => mpfr::rnd_t::RNDA,
        5 => mpfr::rnd_t::RNDF,
        _ => mpfr::rnd_t::RNDNA,
    };
    let im = match r >> 4 {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
        4 => mpfr::rnd_t::RNDA,
        5 => mpfr::rnd_t::RNDF,
        _ => mpfr::rnd_t::RNDNA,
    };
    (re, im)
}

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

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

impl Inner for Complex {
    type Output = mpc_t;
    fn inner(&self) -> &mpc_t {
        let ptr = self as *const _ as *const _;
        unsafe { &*ptr }
    }
}
