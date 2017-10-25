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

use {Assign, Integer, Rational};
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use rational::{ParseRationalError, ValidRational};
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::hash::{Hash, Hasher};
use std::i32;
use std::mem;
use std::str::FromStr;

impl Default for Rational {
    #[inline]
    fn default() -> Rational {
        Rational::new()
    }
}

impl Clone for Rational {
    #[inline]
    fn clone(&self) -> Rational {
        let mut ret = Rational::new();
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Rational) {
        self.assign(source);
    }
}

impl Drop for Rational {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(self.inner_mut());
        }
    }
}

impl Hash for Rational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let (num, den) = self.as_numer_denom();
        num.hash(state);
        den.hash(state);
    }
}

from_borrow! { &'a Rational => Rational }

impl From<Integer> for Rational {
    /// Constructs a `Rational` number from an
    /// [`Integer`](struct.Integer.html).
    ///
    /// This constructor allocates one new
    /// [`Integer`](struct.Integer.html) and reuses the allocation for
    /// `val`.
    #[inline]
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_borrow! { &'a Integer => Rational }

impl From<(Integer, Integer)> for Rational {
    /// Constructs a `Rational` number from a numerator
    /// [`Integer`](struct.Integer.html) and denominator
    /// [`Integer`](struct.Integer.html).
    ///
    /// This constructor does not allocate, as it reuses the
    /// [`Integer`](struct.Integer.html) components.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    #[inline]
    fn from((mut num, mut den): (Integer, Integer)) -> Rational {
        assert_ne!(den.cmp0(), Ordering::Equal, "division by zero");
        let mut dst: Rational = unsafe { mem::uninitialized() };
        {
            let mut num_den = dst.as_mut_numer_denom();
            mem::swap(&mut num, num_den.num());
            mem::swap(&mut den, num_den.den());
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

from_borrow! { (&'a Integer, &'a Integer) => Rational }

macro_rules! from {
    { $Src:ty => $Dst:ty } => {
        impl From<$Src> for $Dst {
            #[inline]
            fn from(t: $Src) -> $Dst {
                let mut ret = <$Dst>::new();
                ret.assign(t);
                ret
            }
        }
    }
}

from! { i32 => Rational }
from! { i64 => Rational }
from! { u32 => Rational }
from! { u64 => Rational }
from! { (i32, i32) => Rational }
from! { (i64, i64) => Rational }
from! { (i32, u32) => Rational }
from! { (i64, u64) => Rational }
from! { (u32, i32) => Rational }
from! { (u64, i64) => Rational }
from! { (u32, u32) => Rational }
from! { (u64, u64) => Rational }

impl FromStr for Rational {
    type Err = ParseRationalError;
    #[inline]
    fn from_str(src: &str) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str(src)?;
        Ok(r)
    }
}

impl Display for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Binary for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl Assign for Rational {
    #[inline]
    fn assign(&mut self, mut other: Rational) {
        self.assign(&other);
        mem::swap(self, &mut other);
    }
}

impl<'a> Assign<&'a Rational> for Rational {
    #[inline]
    fn assign(&mut self, other: &'a Rational) {
        unsafe {
            gmp::mpq_set(self.inner_mut(), other.inner());
        }
    }
}

impl<'a> Assign<&'a Integer> for Rational {
    #[inline]
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(self.inner_mut(), val.inner());
        }
    }
}

macro_rules! assign {
    { $T:ty } => {
        impl Assign<$T> for Rational {
            #[inline]
            fn assign(&mut self, t: $T) {
                // no need to canonicalize, as denominator will be 1.
                let num_den =
                    unsafe { self.as_mut_numer_denom_no_canonicalization() };
                num_den.0.assign(t);
                num_den.1.assign(1);
            }
        }
    };
}

assign!{ Integer }
assign!{ i32 }
assign!{ i64 }
assign!{ u32 }
assign!{ u64 }

assign_ref!{ Rational: i32 }
assign_ref!{ Rational: i64 }
assign_ref!{ Rational: u32 }
assign_ref!{ Rational: u64 }

impl<T, U> Assign<(T, U)> for Rational
where
    Integer: Assign<T> + Assign<U>,
{
    #[inline]
    fn assign(&mut self, rhs: (T, U)) {
        let mut num_den = self.as_mut_numer_denom();
        num_den.num().assign(rhs.0);
        num_den.den().assign(rhs.1);
    }
}

impl<'a, T, U> Assign<&'a (T, U)> for Rational
where
    Integer: Assign<&'a T> + Assign<&'a U>,
{
    #[inline]
    fn assign(&mut self, rhs: &'a (T, U)) {
        let mut num_den = self.as_mut_numer_denom();
        num_den.num().assign(&rhs.0);
        num_den.den().assign(&rhs.1);
    }
}

fn fmt_radix(
    r: &Rational,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = r.to_string_radix(radix);
    if to_upper {
        s.make_ascii_uppercase();
    }
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

from_borrow! { ValidRational<'a> => Rational }

impl Display for ParseRationalError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Rational {}
unsafe impl Sync for Rational {}
