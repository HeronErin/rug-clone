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

use {Assign, Integer};
use cast::cast;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use integer::ParseIntegerError;
use integer::big;
use misc;
use std::{i32, u32};
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::hash::{Hash, Hasher};
use std::mem;
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
            let limbs: usize = cast(size.checked_abs().expect("overflow"));
            let slice = unsafe { slice::from_raw_parts(self.inner().d, limbs) };
            slice.hash(state);
        }
    }
}

impl<T> Assign<T> for Result<Integer, Integer>
where
    for<'a> Result<&'a mut Integer, &'a mut Integer>: Assign<T>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        let ok = {
            let mut m = self.as_mut();
            m.assign(src);
            m.is_ok()
        };
        if self.is_ok() != ok {
            misc::result_swap(self);
        }
    }
}

impl<T> Assign<T> for (Integer, u32)
where
    for<'a, 'b> (&'a mut Integer, &'b mut u32): Assign<T>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        (&mut self.0, &mut self.1).assign(src);
    }
}

impl<T> Assign<T> for (Integer, Integer)
where
    for<'a, 'b> (&'a mut Integer, &'b mut Integer): Assign<T>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        (&mut self.0, &mut self.1).assign(src);
    }
}

impl<T> Assign<T> for (Integer, Integer, Integer)
where
    for<'a, 'b, 'c>
        (&'a mut Integer, &'b mut Integer, &'c mut Integer): Assign<T>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        (&mut self.0, &mut self.1, &mut self.2).assign(src);
    }
}

impl Assign for Integer {
    #[inline]
    fn assign(&mut self, src: Integer) {
        mem::drop(mem::replace(self, src));
    }
}

impl<'a> Assign<&'a Integer> for Integer {
    #[inline]
    fn assign(&mut self, src: &'a Integer) {
        unsafe {
            gmp::mpz_set(self.inner_mut(), src.inner());
        }
    }
}

impl<'a> From<&'a Integer> for Integer {
    #[inline]
    fn from(val: &Integer) -> Self {
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set(ret.inner_mut(), val.inner());
            ret
        }
    }
}

macro_rules! assign {
    { $T:ty, $set:path, $init_set:path } => {
        impl Assign<$T> for Integer {
            #[inline]
            fn assign(&mut self, src: $T) {
                unsafe {
                    $set(self.inner_mut(), src.into());
                }
            }
        }

        impl From<$T> for Integer {
            #[inline]
            fn from(src: $T) -> Self {
                unsafe {
                    let mut dst: Integer = mem::uninitialized();
                    $init_set(dst.inner_mut(), src.into());
                    dst
                }
            }
        }

        assign_deref! { $T => Integer }
    }
}

macro_rules! assign_cast {
    { $New:ty, $Existing:ty } => {
        impl Assign<$New> for Integer {
            #[inline]
            fn assign(&mut self, src: $New) {
                <Integer as Assign<$Existing>>::assign(self, cast(src));
            }
        }

        impl From<$New> for Integer {
            #[inline]
            fn from(src: $New) -> Self {
                <Self as From<$Existing>>::from(cast(src))
            }
        }

        assign_deref! { $New => Integer }
    }
}

assign! { i8, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i16, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i32, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i64, xgmp::mpz_set_i64, xgmp::mpz_init_set_i64 }
#[cfg(target_pointer_width = "32")]
assign_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
assign_cast! { isize, i64 }

assign! { u8, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u16, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u32, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u64, xgmp::mpz_set_u64, xgmp::mpz_init_set_u64 }
#[cfg(target_pointer_width = "32")]
assign_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
assign_cast! { usize, u64 }

impl FromStr for Integer {
    type Err = ParseIntegerError;
    #[inline]
    fn from_str(src: &str) -> Result<Integer, ParseIntegerError> {
        Ok(Integer::from(Integer::parse(src, 10)?))
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

fn fmt_radix(
    i: &Integer,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = String::new();
    big::append_to_string(&mut s, i, radix, to_upper);
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
