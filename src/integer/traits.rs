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
#[cfg(try_from)]
use integer::TryFromIntegerError;
use integer::big;
use std::{i32, u32};
#[cfg(try_from)]
use std::error::Error;
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
        unsafe {
            let mut ret: Integer = mem::uninitialized();
            gmp::mpz_init_set(ret.inner_mut(), self.inner());
            ret
        }
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
    for<'a, 'b, 'c> (
        &'a mut Integer,
        &'b mut Integer,
        &'c mut Integer,
    ): Assign<T>,
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
    fn assign(&mut self, src: &Integer) {
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

#[cfg(try_from)]
macro_rules! try_from {
    ($(($T: ty, $method: ident))*) => { $(
        impl TryFrom<Integer> for $T {
            type Error = TryFromIntegerError;
            fn try_from(value: Integer) -> Result<Self, TryFromIntegerError> {
                TryFrom::try_from(&value)
            }
        }
        impl<'a> TryFrom<&'a Integer> for $T {
            type Error = TryFromIntegerError;
            fn try_from(value: &Integer) -> Result<Self, TryFromIntegerError> {
                value
                    .$method()
                    .ok_or(TryFromIntegerError { _unused: () })
            }
        }
    )* };
}

#[cfg(try_from)]
try_from! {
    (i8, to_i8) (i16, to_i16) (i32, to_i32) (i64, to_i64) (isize, to_isize)
}
#[cfg(all(int_128, try_from))]
try_from! { (i128, to_i128) }
#[cfg(try_from)]
try_from! {
    (u8, to_u8) (u16, to_u16) (u32, to_u32) (u64, to_u64) (usize, to_usize)
}
#[cfg(all(int_128, try_from))]
try_from! { (u128, to_u128) }

macro_rules! assign {
    ($T: ty, $set: path, $init_set: path) => {
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
    };
}

macro_rules! assign_cast {
    ($New: ty, $Existing: ty) => {
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
    };
}

assign! { i8, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i16, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i32, xgmp::mpz_set_i32, gmp::mpz_init_set_si }
assign! { i64, xgmp::mpz_set_i64, xgmp::mpz_init_set_i64 }
#[cfg(target_pointer_width = "32")]
assign_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
assign_cast! { isize, i64 }
#[cfg(int_128)]
assign! { i128, xgmp::mpz_set_i128, xgmp::mpz_init_set_i128 }

assign! { u8, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u16, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u32, xgmp::mpz_set_u32, gmp::mpz_init_set_ui }
assign! { u64, xgmp::mpz_set_u64, xgmp::mpz_init_set_u64 }
#[cfg(target_pointer_width = "32")]
assign_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
assign_cast! { usize, u64 }
#[cfg(int_128)]
assign! { u128, xgmp::mpz_set_u128, xgmp::mpz_init_set_u128 }

impl FromStr for Integer {
    type Err = ParseIntegerError;
    #[inline]
    fn from_str(src: &str) -> Result<Integer, ParseIntegerError> {
        Ok(Integer::from(Integer::parse(src)?))
    }
}

impl Display for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Integer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Integer {
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
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

#[cfg(try_from)]
impl Error for TryFromIntegerError {
    fn description(&self) -> &str {
        "out of range conversion attempted"
    }
}

#[cfg(try_from)]
impl Display for TryFromIntegerError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self.description(), f)
    }
}

unsafe impl Send for Integer {}
unsafe impl Sync for Integer {}

#[cfg(test)]
mod tests {
    #[cfg(try_from)]
    #[test]
    fn check_fallible_conversions() {
        use {Assign, Integer};
        let mut i = Integer::from(0x7f);
        assert_eq!(i8::try_from(&i).unwrap(), 0x7f);
        i <<= 1;
        assert!(i8::try_from(&i).is_err());
        assert_eq!(u8::try_from(&i).unwrap(), 0xfe);
        i <<= 1;
        assert!(u8::try_from(&i).is_err());
        i <<= 6;
        assert_eq!(i16::try_from(&i).unwrap(), 0x7f << 8);
        i <<= 1;
        assert!(i16::try_from(&i).is_err());
        assert_eq!(u16::try_from(&i).unwrap(), 0xfe << 8);
        i <<= 1;
        assert!(u16::try_from(&i).is_err());
        i <<= 14;
        assert_eq!(i32::try_from(&i).unwrap(), 0x7f << 24);
        i <<= 1;
        assert!(i32::try_from(&i).is_err());
        assert_eq!(u32::try_from(&i).unwrap(), 0xfe << 24);
        i <<= 1;
        assert!(u32::try_from(&i).is_err());
        i <<= 30;
        assert_eq!(i64::try_from(&i).unwrap(), 0x7f << 56);
        i <<= 1;
        assert!(i64::try_from(&i).is_err());
        assert_eq!(u64::try_from(&i).unwrap(), 0xfe << 56);
        i <<= 1;
        assert!(u64::try_from(&i).is_err());
        #[cfg(int_128)]
        {
            i <<= 62;
            assert_eq!(i128::try_from(&i).unwrap(), 0x7f << 120);
            i <<= 1;
            assert!(i128::try_from(&i).is_err());
            assert_eq!(u128::try_from(&i).unwrap(), 0xfe << 120);
            i <<= 1;
            assert!(u128::try_from(&i).is_err());
        }

        i.assign(-1);
        assert!(u8::try_from(&i).is_err());
        assert!(u16::try_from(&i).is_err());
        assert!(u32::try_from(&i).is_err());
        assert!(u64::try_from(&i).is_err());
        #[cfg(int_128)]
        assert!(u128::try_from(&i).is_err());
        i <<= 7;
        assert_eq!(i8::try_from(&i).unwrap(), -0x80);
        i <<= 1;
        assert!(i8::try_from(&i).is_err());
        i <<= 7;
        assert_eq!(i16::try_from(&i).unwrap(), -0x80 << 8);
        i <<= 1;
        assert!(i16::try_from(&i).is_err());
        i <<= 15;
        assert_eq!(i32::try_from(&i).unwrap(), -0x80 << 24);
        i <<= 1;
        assert!(i32::try_from(&i).is_err());
        i <<= 31;
        assert_eq!(i64::try_from(&i).unwrap(), -0x80 << 56);
        i <<= 1;
        assert!(i64::try_from(&i).is_err());
        #[cfg(int_128)]
        {
            i <<= 63;
            assert_eq!(i128::try_from(&i).unwrap(), -0x80 << 120);
            i <<= 1;
            assert!(i128::try_from(&i).is_err());
        }
    }
}
