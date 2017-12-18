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

use {Assign, Integer};
use big_integer;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use integer::{ParseIntegerError, ValidInteger};
use std::{i32, u32};
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::hash::{Hash, Hasher};
use std::mem;
use std::os::raw::{c_long, c_ulong};
use std::slice;
use std::str::FromStr;

impl Default for Integer {
    #[inline]
    fn default() -> Integer {
        Integer::new()
    }
}

impl Clone for Integer {
    #[inline]
    fn clone(&self) -> Integer {
        let mut ret = Integer::new();
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Integer) {
        self.assign(source);
    }
}

impl Drop for Integer {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::mpz_clear(self.inner_mut());
        }
    }
}

impl Hash for Integer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let size = self.inner().size;
        size.hash(state);
        if size != 0 {
            let limbs = size.checked_abs().expect("overflow") as usize;
            let slice =
                unsafe { slice::from_raw_parts(self.inner().d, limbs) };
            slice.hash(state);
        }
    }
}

impl<'a> From<&'a Integer> for Integer {
    #[inline]
    fn from(val: &Integer) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set(ret.inner_mut(), val.inner());
            ret
        }
    }
}

impl From<i32> for Integer {
    #[inline]
    fn from(val: i32) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_si(ret.inner_mut(), val.into());
            ret
        }
    }
}

impl From<i64> for Integer {
    #[inline]
    fn from(val: i64) -> Integer {
        if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
            unsafe {
                let mut ret: Integer = mem::uninitialized();
                gmp::mpz_init_set_si(ret.inner_mut(), val as c_long);
                ret
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

impl From<u32> for Integer {
    #[inline]
    fn from(val: u32) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_ui(ret.inner_mut(), val.into());
            ret
        }
    }
}

impl From<u64> for Integer {
    #[inline]
    fn from(val: u64) -> Integer {
        if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
            unsafe {
                let mut ret: Integer = mem::uninitialized();
                gmp::mpz_init_set_ui(ret.inner_mut(), val as c_ulong);
                ret
            }
        } else {
            let mut i = Integer::new();
            i.assign(val);
            i
        }
    }
}

impl FromStr for Integer {
    type Err = ParseIntegerError;
    #[inline]
    fn from_str(src: &str) -> Result<Integer, ParseIntegerError> {
        let mut i = Integer::new();
        i.assign_str(src)?;
        Ok(i)
    }
}

impl Display for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl Assign for Integer {
    #[inline]
    fn assign(&mut self, mut other: Integer) {
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Integer> for Integer {
    #[inline]
    fn assign(&mut self, other: &'a Integer) {
        unsafe {
            gmp::mpz_set(self.inner_mut(), other.inner());
        }
    }
}

impl Assign<i32> for Integer {
    #[inline]
    fn assign(&mut self, val: i32) {
        unsafe {
            xgmp::mpz_set_i32(self.inner_mut(), val);
        }
    }
}

impl Assign<i64> for Integer {
    #[inline]
    fn assign(&mut self, val: i64) {
        unsafe {
            xgmp::mpz_set_i64(self.inner_mut(), val);
        }
    }
}

impl Assign<u32> for Integer {
    #[inline]
    fn assign(&mut self, val: u32) {
        unsafe {
            xgmp::mpz_set_u32(self.inner_mut(), val);
        }
    }
}

impl Assign<u64> for Integer {
    #[inline]
    fn assign(&mut self, val: u64) {
        unsafe {
            xgmp::mpz_set_u64(self.inner_mut(), val);
        }
    }
}

assign_ref!{ Integer: i32 }
assign_ref!{ Integer: i64 }
assign_ref!{ Integer: u32 }
assign_ref!{ Integer: u64 }

fn fmt_radix(
    i: &Integer,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = String::new();
    big_integer::append_to_string(&mut s, i, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

from_borrow! { ValidInteger<'a> => Integer }

impl Display for ParseIntegerError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Integer {}
unsafe impl Sync for Integer {}
