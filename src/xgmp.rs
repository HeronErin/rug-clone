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

use gmp_mpfr_sys::gmp::{self, mpq_t};
use std::os::raw::{c_long, c_ulong};

pub unsafe fn mpq_inv_check_0(rop: *mut mpq_t, op: *const mpq_t) {
    assert_ne!(gmp::mpq_sgn(op), 0, "division by zero");
    gmp::mpq_inv(rop, op);
}

pub unsafe fn mpq_mul_2exp_si(
    rop: *mut mpq_t,
    op1: *const mpq_t,
    op2: c_long,
) {
    if op2 >= 0 {
        gmp::mpq_mul_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpq_div_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpq_div_2exp_si(
    rop: *mut mpq_t,
    op1: *const mpq_t,
    op2: c_long,
) {
    if op2 >= 0 {
        gmp::mpq_div_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpq_mul_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpq_pow_ui(rop: *mut mpq_t, op1: *const mpq_t, op2: c_ulong) {
    let rop_num = gmp::mpq_numref(rop);
    let rop_den = gmp::mpq_denref(rop);
    let op1_num = gmp::mpq_numref(op1 as *mut _) as *const _;
    let op1_den = gmp::mpq_denref(op1 as *mut _) as *const _;
    gmp::mpz_pow_ui(rop_num, op1_num, op2);
    gmp::mpz_pow_ui(rop_den, op1_den, op2);
}

pub unsafe fn mpq_pow_si(rop: *mut mpq_t, op1: *const mpq_t, op2: c_long) {
    if op2 < 0 {
        assert_ne!(gmp::mpq_sgn(op1), 0, "division by zero");
        gmp::mpq_inv(rop, op1);
        mpq_pow_ui(rop, rop, op2.wrapping_neg() as c_ulong);
    } else {
        mpq_pow_ui(rop, op1, op2 as c_ulong);
    };
}
