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
use integer::ParseIntegerError;
use misc;
use ops::AssignTo;
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
            let slice = unsafe { slice::from_raw_parts(self.inner().d, limbs) };
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

impl<T> From<T> for Integer
where
    T: AssignTo<Integer>,
{
    #[inline]
    fn from(src: T) -> Integer {
        src.to_new()
    }
}

impl<T> Assign<T> for Integer
where
    T: AssignTo<Integer>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl<T> Assign<T> for Result<Integer, Integer>
where
    T: for<'a> AssignTo<Result<&'a mut Integer, &'a mut Integer>>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        let ok = {
            let mut m = self.as_mut();
            src.assign_to(&mut m);
            m.is_ok()
        };
        if self.is_ok() != ok {
            misc::result_swap(self);
        }
    }
}

impl<'a, T> Assign<T> for Result<&'a mut Integer, &'a mut Integer>
where
    T: AssignTo<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl<T> Assign<T> for (Integer, u32)
where
    T: for<'a, 'b> AssignTo<(&'a mut Integer, &'b mut u32)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(&mut (&mut self.0, &mut self.1));
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Integer, &'b mut u32)
where
    T: AssignTo<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl<T> Assign<T> for (Integer, Integer)
where
    T: for<'a, 'b> AssignTo<(&'a mut Integer, &'b mut Integer)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(&mut (&mut self.0, &mut self.1));
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Integer, &'b mut Integer)
where
    T: AssignTo<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl<T> Assign<T> for (Integer, Integer, Integer)
where
    T: for<'a, 'b, 'c> AssignTo<
        (&'a mut Integer, &'b mut Integer, &'c mut Integer),
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(&mut (&mut self.0, &mut self.1, &mut self.2));
    }
}

impl<'a, 'b, 'c, T> Assign<T>
    for (&'a mut Integer, &'b mut Integer, &'c mut Integer)
where
    T: AssignTo<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl AssignTo<Integer> for i32 {
    #[inline]
    fn assign_to(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_i32(dst.inner_mut(), self);
        }
    }

    #[inline]
    fn to_new(self) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_si(ret.inner_mut(), self.into());
            ret
        }
    }
}

assign_to!{ i32 => Integer }

impl AssignTo<Integer> for i64 {
    #[inline]
    fn assign_to(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_i64(dst.inner_mut(), self);
        }
    }

    #[inline]
    fn to_new(self) -> Integer {
        let mut ret: Integer;
        if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
            unsafe {
                ret = mem::uninitialized();
                gmp::mpz_init_set_si(ret.inner_mut(), self as c_long);
            }
        } else {
            ret = Integer::new();
            self.assign_to(&mut ret);
        }
        ret
    }
}

assign_to!{ i64 => Integer }

impl AssignTo<Integer> for u32 {
    #[inline]
    fn assign_to(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_u32(dst.inner_mut(), self);
        }
    }

    #[inline]
    fn to_new(self) -> Integer {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set_ui(ret.inner_mut(), self.into());
            ret
        }
    }
}

assign_to!{ u32 => Integer }

impl AssignTo<Integer> for u64 {
    #[inline]
    fn assign_to(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_u64(dst.inner_mut(), self);
        }
    }

    #[inline]
    fn to_new(self) -> Integer {
        let mut ret: Integer;
        if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
            unsafe {
                ret = mem::uninitialized();
                gmp::mpz_init_set_ui(ret.inner_mut(), self as c_ulong);
            }
        } else {
            ret = Integer::new();
            ret.assign(self);
        }
        ret
    }
}

assign_to!{ u64 => Integer }

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

impl Display for ParseIntegerError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Integer {}
unsafe impl Sync for Integer {}
