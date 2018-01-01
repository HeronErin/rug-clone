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

use Float;
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use big_float::ordering1;
use ext::mpfr as xmpfr;
use gmp_mpfr_sys::mpfr;
use inner::Inner;
use std::{i32, u32};
use std::cmp::Ordering;

impl PartialEq for Float {
    #[inline]
    fn eq(&self, other: &Float) -> bool {
        unsafe { mpfr::equal_p(self.inner(), other.inner()) != 0 }
    }
}

impl PartialOrd for Float {
    #[inline]
    fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
        unsafe {
            match mpfr::unordered_p(self.inner(), other.inner()) {
                0 => Some(ordering1(mpfr::cmp(self.inner(), other.inner()))),
                _ => None,
            }
        }
    }

    #[inline]
    fn lt(&self, other: &Float) -> bool {
        unsafe { mpfr::less_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn le(&self, other: &Float) -> bool {
        unsafe { mpfr::lessequal_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn gt(&self, other: &Float) -> bool {
        unsafe { mpfr::greater_p(self.inner(), other.inner()) != 0 }
    }

    #[inline]
    fn ge(&self, other: &Float) -> bool {
        unsafe { mpfr::greaterequal_p(self.inner(), other.inner()) != 0 }
    }
}

macro_rules! cmp {
    { $T:ty, $eval:expr } => {
        impl PartialEq<$T> for Float {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                <Float as PartialOrd<$T>>::partial_cmp(self, other)
                    == Some(Ordering::Equal)
            }
        }

        impl PartialEq<Float> for $T {
            #[inline]
            fn eq(&self, other: &Float) -> bool {
                <Float as PartialOrd<$T>>::partial_cmp(other, self)
                    == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Float {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                if self.is_nan() {
                    None
                } else {
                    Some(ordering1($eval(self.inner(), other)))
                }
            }
        }

        impl PartialOrd<Float> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
                <Float as PartialOrd<$T>>::partial_cmp(other, self)
                    .map(Ordering::reverse)
            }
        }
    }
}

#[cfg(feature = "integer")]
cmp! { Integer, |f, t: &Integer| unsafe { mpfr::cmp_z(f, t.inner()) } }
#[cfg(feature = "rational")]
cmp! { Rational, |f, t: &Rational| unsafe { mpfr::cmp_q(f, t.inner()) } }

cmp! { i8, |f, t: &i8| unsafe { mpfr::cmp_si(f, (*t).into()) } }
cmp! { i16, |f, t: &i16| unsafe { mpfr::cmp_si(f, (*t).into()) } }
cmp! { i32, |f, t: &i32| unsafe { mpfr::cmp_si(f, (*t).into()) } }
cmp! { i64, |f, t: &i64| unsafe { xmpfr::cmp_i64(f, *t) } }
#[cfg(target_pointer_width = "32")]
cmp! { isize, |f, t: &isize| unsafe { mpfr::cmp_si(f, (*t as i32).into()) } }
#[cfg(target_pointer_width = "64")]
cmp! { isize, |f, t: &isize| unsafe { xmpfr::cmp_i64(f, *t as i64) } }

cmp! { u8, |f, t: &u8| unsafe { mpfr::cmp_ui(f, (*t).into()) } }
cmp! { u16, |f, t: &u16| unsafe { mpfr::cmp_ui(f, (*t).into()) } }
cmp! { u32, |f, t: &u32| unsafe { mpfr::cmp_ui(f, (*t).into()) } }
cmp! { u64, |f, t: &u64| unsafe { xmpfr::cmp_u64(f, *t) } }
#[cfg(target_pointer_width = "32")]
cmp! { usize, |f, t: &usize| unsafe { mpfr::cmp_ui(f, (*t as u32).into()) } }
#[cfg(target_pointer_width = "64")]
cmp! { usize, |f, t: &usize| unsafe { xmpfr::cmp_u64(f, *t as u64) } }

cmp! { f32, |f, t: &f32| unsafe { mpfr::cmp_d(f, (*t).into()) } }
cmp! { f64, |f, t: &f64| unsafe { mpfr::cmp_d(f, *t) } }
