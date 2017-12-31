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
use ops::AssignInto;
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

impl<T> Assign<T> for Integer
where
    T: AssignInto<Integer>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(self);
    }
}

impl<T> Assign<T> for Result<Integer, Integer>
where
    T: for<'a> AssignInto<Result<&'a mut Integer, &'a mut Integer>>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        let ok = {
            let mut m = self.as_mut();
            src.assign_into(&mut m);
            m.is_ok()
        };
        if self.is_ok() != ok {
            misc::result_swap(self);
        }
    }
}

impl<'a, T> Assign<T> for Result<&'a mut Integer, &'a mut Integer>
where
    T: AssignInto<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(self);
    }
}

impl<T> Assign<T> for (Integer, u32)
where
    T: for<'a, 'b> AssignInto<(&'a mut Integer, &'b mut u32)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(&mut (&mut self.0, &mut self.1));
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Integer, &'b mut u32)
where
    T: AssignInto<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(self);
    }
}

impl<T> Assign<T> for (Integer, Integer)
where
    T: for<'a, 'b> AssignInto<(&'a mut Integer, &'b mut Integer)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(&mut (&mut self.0, &mut self.1));
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Integer, &'b mut Integer)
where
    T: AssignInto<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(self);
    }
}

impl<T> Assign<T> for (Integer, Integer, Integer)
where
    T: for<'a, 'b, 'c> AssignInto<
        (&'a mut Integer, &'b mut Integer, &'c mut Integer),
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(&mut (&mut self.0, &mut self.1, &mut self.2));
    }
}

impl<'a, 'b, 'c, T> Assign<T>
    for (&'a mut Integer, &'b mut Integer, &'c mut Integer)
where
    T: AssignInto<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_into(self);
    }
}

impl AssignInto<Integer> for Integer {
    #[inline]
    fn assign_into(mut self, dst: &mut Integer) {
        mem::swap(&mut self, dst);
    }
}

impl<'a> AssignInto<Integer> for &'a Integer {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            gmp::mpz_set(dst.inner_mut(), self.inner());
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

macro_rules! assign_into_cast {
    { $New:ty, $Existing:ty } => {
        impl AssignInto<Integer> for $New {
            #[inline]
            fn assign_into(self, dst: &mut Integer) {
                <$Existing as AssignInto<Integer>>::assign_into(
                    self as $Existing,
                    dst,
                );
            }
        }

        impl From<$New> for Integer {
            #[inline]
            fn from(src: $New) -> Self {
                <Self as From<$Existing>>::from(src as $Existing)
            }
        }

        assign_into_deref! { $New => Integer }
    }
}

assign_into_cast! { i8, i32 }
assign_into_cast! { i16, i32 }

impl AssignInto<Integer> for i32 {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_i32(dst.inner_mut(), self);
        }
    }
}

impl From<i32> for Integer {
    #[inline]
    fn from(src: i32) -> Self {
        unsafe {
            let mut dst: Integer = mem::uninitialized();
            gmp::mpz_init_set_si(dst.inner_mut(), src.into());
            dst
        }
    }
}

assign_into_deref! { i32 => Integer }

impl AssignInto<Integer> for i64 {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_i64(dst.inner_mut(), self);
        }
    }
}

impl From<i64> for Integer {
    #[inline]
    fn from(src: i64) -> Self {
        let mut dst: Integer;
        if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
            unsafe {
                dst = mem::uninitialized();
                gmp::mpz_init_set_si(dst.inner_mut(), src as c_long);
            }
        } else {
            dst = Integer::new();
            src.assign_into(&mut dst);
        }
        dst
    }
}

assign_into_deref! { i64 => Integer }

#[cfg(target_pointer_width = "16")]
assign_into_cast! { isize, i16 }
#[cfg(target_pointer_width = "32")]
assign_into_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
assign_into_cast! { isize, i64 }

assign_into_cast! { u8, u32 }
assign_into_cast! { u16, u32 }

impl AssignInto<Integer> for u32 {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_u32(dst.inner_mut(), self);
        }
    }
}

impl From<u32> for Integer {
    #[inline]
    fn from(src: u32) -> Self {
        unsafe {
            let mut dst: Integer = mem::uninitialized();
            gmp::mpz_init_set_ui(dst.inner_mut(), src.into());
            dst
        }
    }
}

assign_into_deref! { u32 => Integer }

impl AssignInto<Integer> for u64 {
    #[inline]
    fn assign_into(self, dst: &mut Integer) {
        unsafe {
            xgmp::mpz_set_u64(dst.inner_mut(), self);
        }
    }
}

impl From<u64> for Integer {
    #[inline]
    fn from(src: u64) -> Self {
        let mut dst: Integer;
        if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
            unsafe {
                dst = mem::uninitialized();
                gmp::mpz_init_set_ui(dst.inner_mut(), src as c_ulong);
            }
        } else {
            dst = Integer::new();
            dst.assign(src);
        }
        dst
    }
}

assign_into_deref! { u64 => Integer }

#[cfg(target_pointer_width = "16")]
assign_into_cast! { usize, u16 }
#[cfg(target_pointer_width = "32")]
assign_into_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
assign_into_cast! { usize, u64 }

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
