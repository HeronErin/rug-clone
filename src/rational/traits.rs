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
use big_rational;
use gmp_mpfr_sys::gmp;
use inner::{Inner, InnerMut};
use ops::AssignTo;
use rational::ParseRationalError;
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerHex, Octal,
               UpperHex};
use std::hash::{Hash, Hasher};
use std::i32;
use std::mem;
use std::ptr;
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

impl<T> From<T> for Rational
where
    T: AssignTo<Rational>,
{
    #[inline]
    fn from(src: T) -> Rational {
        src.to_new()
    }
}

impl<T> Assign<T> for Rational
where
    T: AssignTo<Rational>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
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

impl<Num> AssignTo<Rational> for Num
where
    Integer: Assign<Num> + From<Num>,
{
    #[inline]
    fn assign_to(self, dst: &mut Rational) {
        // no need to canonicalize, as denominator will be 1.
        let num_den = unsafe { dst.as_mut_numer_denom_no_canonicalization() };
        num_den.0.assign(self);
        <Integer as Assign<u32>>::assign(num_den.1, 1);
    }

    #[inline]
    fn to_new(self) -> Rational {
        let num = Integer::from(self);
        let den = <Integer as From<u32>>::from(1);
        let mut dst: Rational = unsafe { mem::uninitialized() };
        unsafe {
            let num_den = dst.as_mut_numer_denom_no_canonicalization();
            ptr::copy_nonoverlapping(&num, num_den.0, 1);
            ptr::copy_nonoverlapping(&den, num_den.1, 1);
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

impl<Num, Den> AssignTo<Rational> for (Num, Den)
where
    Integer: Assign<Num> + Assign<Den> + From<Num> + From<Den>,
{
    #[inline]
    fn assign_to(self, dst: &mut Rational) {
        let mut num_den = dst.as_mut_numer_denom();
        num_den.num().assign(self.0);
        num_den.den().assign(self.1);
    }

    #[inline]
    fn to_new(self) -> Rational {
        let den = Integer::from(self.1);
        assert_ne!(den.cmp0(), Ordering::Equal, "division by zero");
        let num = Integer::from(self.0);
        let mut dst: Rational = unsafe { mem::uninitialized() };
        unsafe {
            let mut num_den = dst.as_mut_numer_denom();
            ptr::copy_nonoverlapping(&num, num_den.num(), 1);
            ptr::copy_nonoverlapping(&den, num_den.den(), 1);
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

impl<'a, Num, Den> AssignTo<Rational> for &'a (Num, Den)
where
    Integer: Assign<&'a Num> + Assign<&'a Den>,
{
    #[inline]
    fn assign_to(self, dst: &mut Rational) {
        let mut num_den = dst.as_mut_numer_denom();
        num_den.num().assign(&self.0);
        num_den.den().assign(&self.1);
    }
}

fn fmt_radix(
    r: &Rational,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = String::new();
    big_rational::append_to_string(&mut s, r, radix, to_upper);
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    f.pad_integral(!neg, prefix, buf)
}

impl Display for ParseRationalError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Rational {}
unsafe impl Sync for Rational {}
