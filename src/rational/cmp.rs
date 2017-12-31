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
use ext::gmp as xgmp;
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

impl PartialEq<Integer> for Rational {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        unsafe { gmp::mpq_cmp_z(self.inner(), other.inner()) == 0 }
    }
}

impl PartialEq<Rational> for Integer {
    #[inline]
    fn eq(&self, other: &Rational) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<Integer> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        let ord = unsafe { gmp::mpq_cmp_z(self.inner(), other.inner()) };
        Some(ord.cmp(&0))
    }
}

impl PartialOrd<Rational> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        other.partial_cmp(self).map(Ordering::reverse)
    }
}

macro_rules! cmp {
    { $T:ty, $cmp:path } => {
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                unsafe { $cmp(self.inner(), (*other) as _, 1) == 0 }
            }
        }

        impl PartialEq<Rational> for $T {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                <Rational as PartialEq<$T>>::eq(other, self)
            }
        }

        impl PartialOrd<$T> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                let ord = unsafe { $cmp(self.inner(), (*other) as _, 1) };
                Some(ord.cmp(&0))
            }
        }

        impl PartialOrd<Rational> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                <Rational as PartialOrd<$T>>::partial_cmp(other, self)
                    .map(Ordering::reverse)
            }
        }
    }
}

cmp! { i8, gmp::mpq_cmp_si }
cmp! { i16, gmp::mpq_cmp_si }
cmp! { i32, gmp::mpq_cmp_si }
cmp! { i64, xgmp::mpq_cmp_i64 }
#[cfg(target_pointer_width = "32")]
cmp! { isize, gmp::mpq_cmp_si }
#[cfg(target_pointer_width = "64")]
cmp! { isize, xgmp::mpq_cmp_i64 }

cmp! { u8, gmp::mpq_cmp_ui }
cmp! { u16, gmp::mpq_cmp_ui }
cmp! { u32, gmp::mpq_cmp_ui }
cmp! { u64, xgmp::mpq_cmp_u64 }
#[cfg(target_pointer_width = "32")]
cmp! { usize, gmp::mpq_cmp_ui }
#[cfg(target_pointer_width = "64")]
cmp! { usize, xgmp::mpq_cmp_u64 }

macro_rules! cross {
    { $Num:ty; $Den:ty } => {
        impl PartialEq<($Num, $Den)> for Rational {
            #[inline]
            fn eq(&self, other: &($Num, $Den)) -> bool {
                self.eq(&*SmallRational::from(*other))
            }
        }
        impl PartialEq<Rational> for ($Num, $Den) {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                SmallRational::from(*self).eq(other)
            }
        }
        impl PartialOrd<($Num, $Den)> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &($Num, $Den)) -> Option<Ordering> {
                self.partial_cmp(&*SmallRational::from(*other))
            }
        }
        impl PartialOrd<Rational> for ($Num, $Den) {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                SmallRational::from(*self).partial_cmp(other)
            }
        }
    }
}

// (Major, Major), (Major, Minor*), (Minor*, Major)
macro_rules! matrix {
    { $Major:ty $(; $Minor:ty)* } => {
        cross! { $Major; $Major }
        $( cross! { $Major; $Minor } )*
        $( cross! { $Minor; $Major } )*
    }
}

matrix! { u8 }
matrix! { i8; u8 }
matrix! { u16; i8; u8 }
matrix! { i16; u16; i8; u8 }
matrix! { u32; i16; u16; i8; u8 }
matrix! { i32; u32; i16; u16; i8; u8 }
matrix! { usize; i32; u32; i16; u16; i8; u8 }
matrix! { isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { i64; u64; isize; usize; i32; u32; i16; u16; i8; u8 }

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
