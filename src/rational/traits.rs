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
use big_rational::make_string;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use rational::{ParseRationalError, ValidRational};
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

impl<Num> From<Num> for Rational
where
    Integer: From<Num>,
{
    #[inline]
    fn from(num: Num) -> Rational {
        let mut num = Integer::from(num);
        let mut den = <Integer as From<u32>>::from(1);
        let mut dst: Rational = unsafe { mem::uninitialized() };
        {
            let num_den =
                unsafe { dst.as_mut_numer_denom_no_canonicalization() };
            mem::swap(&mut num, num_den.0);
            mem::swap(&mut den, num_den.1);
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

impl<Num, Den> From<(Num, Den)> for Rational
where
    Integer: From<Num> + From<Den>,
{
    #[inline]
    fn from((num, den): (Num, Den)) -> Rational {
        let mut den = Integer::from(den);
        assert_ne!(den.cmp0(), Ordering::Equal, "division by zero");
        let mut num = Integer::from(num);
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

impl<Num> Assign<Num> for Rational
where
    Integer: Assign<Num>,
{
    #[inline]
    fn assign(&mut self, rhs: Num) {
        // no need to canonicalize, as denominator will be 1.
        let num_den = unsafe { self.as_mut_numer_denom_no_canonicalization() };
        num_den.0.assign(rhs);
        <Integer as Assign<u32>>::assign(num_den.1, 1);
    }
}

impl<Num, Den> Assign<(Num, Den)> for Rational
where
    Integer: Assign<Num> + Assign<Den>,
{
    #[inline]
    fn assign(&mut self, rhs: (Num, Den)) {
        let mut num_den = self.as_mut_numer_denom();
        num_den.num().assign(rhs.0);
        num_den.den().assign(rhs.1);
    }
}

impl<'a, Num, Den> Assign<&'a (Num, Den)> for Rational
where
    Integer: Assign<&'a Num> + Assign<&'a Den>,
{
    #[inline]
    fn assign(&mut self, rhs: &'a (Num, Den)) {
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
    let s = make_string(r, radix, to_upper);
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
