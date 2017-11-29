// Copyright © 2016–2017 University of Malta

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

use std::mem;
use std::ptr;

pub fn trunc_f64_to_f32(f: f64) -> f32 {
    // f as f32 might round away from zero, so we need to clear
    // the least significant bits of f.
    // * If f is a nan, we do NOT want to clear any mantissa bits,
    //   as this may change f into +/- infinity.
    // * If f is +/- infinity, the bits are already zero, so the
    //   masking has no effect.
    // * If f is subnormal, f as f32 will be zero anyway.
    if !f.is_nan() {
        let u: u64 = unsafe { mem::transmute(f) };
        // f64 has 29 more significant bits than f32.
        let trunc_u = u & (!0 << 29);
        let trunc_f: f64 = unsafe { mem::transmute(trunc_u) };
        trunc_f as f32
    } else {
        f as f32
    }
}

// The commented out function results in longer x86_64 asm.
// See: https://github.com/rust-lang/rust/issues/42870
//
// pub fn result_swap<T>(r: &mut Result<T, T>) {
//     unsafe {
//         let old = ptr::read(r);
//         let new = match old {
//             Ok(t) => Err(t),
//             Err(t) => Ok(t),
//         };
//         ptr::write(r, new);
//     }
// }
pub fn result_swap<T>(r: &mut Result<T, T>) {
    unsafe {
        if r.is_ok() {
            let val = match *r {
                Ok(ref mut val) => ptr::read(val),
                Err(_) => unreachable!(),
            };
            ptr::write(r, Err(val));
        } else {
            let val = match *r {
                Err(ref mut val) => ptr::read(val),
                Ok(_) => unreachable!(),
            };
            ptr::write(r, Ok(val));
        }
    }
}
