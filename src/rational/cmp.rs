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

use {Integer, Rational};
use gmp_mpfr_sys::gmp;
use inner::Inner;
use rational::SmallRational;
use std::cmp::Ordering;
use std::i32;

impl Eq for Rational {}

impl Ord for Rational {
    #[inline]
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    #[inline]
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $T:ty, $eq:expr, $cmp:expr } => {
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                $eq(self.inner(), other)
            }
        }

        impl PartialEq<Rational> for $T {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<$T> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                Some($cmp(self.inner(), other))
            }
        }

        impl PartialOrd<Rational> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    }
}

cmp! {
    Integer,
    |r, t: &Integer| unsafe { gmp::mpq_cmp_z(r, t.inner()) } == 0,
    |r, t: &Integer| unsafe { gmp::mpq_cmp_z(r, t.inner()) }.cmp(&0)
}
cmp! {
    i32,
    |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1) } == 0,
    |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1) }.cmp(&0)
}
cmp! {
    u32,
    |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1) } == 0,
    |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1) }.cmp(&0)
}

macro_rules! cmp_small_rat {
    { $T:ty } => {
        cmp! {
            $T,
            |r, t: &$T| unsafe {
                gmp::mpq_equal(r, SmallRational::from(*t).inner())
            } != 0,
            |r, t: &$T| unsafe {
                gmp::mpq_cmp(r, SmallRational::from(*t).inner())
            }.cmp(&0)
        }
    };
}

cmp_small_rat! { i64 }
cmp_small_rat! { u64 }
cmp_small_rat! { (i32, i32) }
cmp_small_rat! { (i64, i64) }
cmp_small_rat! { (i32, u32) }
cmp_small_rat! { (i64, u64) }
cmp_small_rat! { (u32, i32) }
cmp_small_rat! { (u64, i64) }
cmp_small_rat! { (u32, u32) }
cmp_small_rat! { (u64, u64) }

#[cfg(test)]
mod tests {
    use Rational;
    use std::{i32, u32};
    use std::cmp::Ordering;

    #[test]
    fn check_cmp_frac() {
        let zero = Rational::new();
        let u = [0, 1, 100, u32::MAX];
        let s = [i32::MIN, -100, -1, 0, 1, 100, i32::MAX];
        for &n in &u {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
        }
        for &n in &s {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert_eq!(zero.partial_cmp(&(n, d)), ans);
                    assert_eq!(zero.partial_cmp(&Rational::from((n, d))), ans);
                }
            }
        }
    }
}
