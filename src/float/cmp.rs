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

use Float;
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use cast::cast;
use ext::mpfr as xmpfr;
use float::big::ordering1;
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
    { $T:ty } => {
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

        impl PartialOrd<Float> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Float) -> Option<Ordering> {
                <Float as PartialOrd<$T>>::partial_cmp(other, self)
                    .map(Ordering::reverse)
            }
        }
    }
}

macro_rules! cmp_i {
    { $T:ty, $eval:expr } => {
        cmp! { $T }

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
    }
}

macro_rules! cmp_f {
    { $T:ty, $eval:expr } => {
        cmp! { $T }

        impl PartialOrd<$T> for Float {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                if self.is_nan() || other.is_nan() {
                    None
                } else {
                    Some(ordering1($eval(self.inner(), other)))
                }
            }
        }
    }
}

#[cfg(feature = "integer")]
cmp_i! { Integer, |f, t: &Integer| unsafe { mpfr::cmp_z(f, t.inner()) } }
#[cfg(feature = "rational")]
cmp_i! { Rational, |f, t: &Rational| unsafe { mpfr::cmp_q(f, t.inner()) } }

cmp_i! { i8, |f, t: &i8| unsafe { mpfr::cmp_si(f, cast(*t)) } }
cmp_i! { i16, |f, t: &i16| unsafe { mpfr::cmp_si(f, cast(*t)) } }
cmp_i! { i32, |f, t: &i32| unsafe { mpfr::cmp_si(f, cast(*t)) } }
cmp_i! { i64, |f, t: &i64| unsafe { xmpfr::cmp_i64(f, *t) } }
#[cfg(target_pointer_width = "32")]
cmp_i! { isize, |f, t: &isize| unsafe { mpfr::cmp_si(f, cast(*t)) } }
#[cfg(target_pointer_width = "64")]
cmp_i! { isize, |f, t: &isize| unsafe { xmpfr::cmp_i64(f, cast(*t)) } }

cmp_i! { u8, |f, t: &u8| unsafe { mpfr::cmp_ui(f, cast(*t)) } }
cmp_i! { u16, |f, t: &u16| unsafe { mpfr::cmp_ui(f, cast(*t)) } }
cmp_i! { u32, |f, t: &u32| unsafe { mpfr::cmp_ui(f, cast(*t)) } }
cmp_i! { u64, |f, t: &u64| unsafe { xmpfr::cmp_u64(f, *t) } }
#[cfg(target_pointer_width = "32")]
cmp_i! { usize, |f, t: &usize| unsafe { mpfr::cmp_ui(f, cast(*t)) } }
#[cfg(target_pointer_width = "64")]
cmp_i! { usize, |f, t: &usize| unsafe { xmpfr::cmp_u64(f, cast(*t)) } }

cmp_f! { f32, |f, t: &f32| unsafe { mpfr::cmp_d(f, cast(*t)) } }
cmp_f! { f64, |f, t: &f64| unsafe { mpfr::cmp_d(f, *t) } }

#[cfg(test)]
mod tests {
    use Float;
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    use std::{f32, f64, i32, u32};
    #[cfg(feature = "integer")]
    use std::str::FromStr;

    #[test]
    fn check_cmp_others() {
        let work_prec = 20;
        let check_prec = 100;
        let f = [
            Float::with_val(work_prec, Special::Zero),
            Float::with_val(work_prec, Special::NegZero),
            Float::with_val(work_prec, Special::Infinity),
            Float::with_val(work_prec, Special::NegInfinity),
            Float::with_val(work_prec, Special::Nan),
            Float::with_val(work_prec, 1),
            Float::with_val(work_prec, -1),
            Float::with_val(work_prec, 999999e100),
            Float::with_val(work_prec, 999999e-100),
            Float::with_val(work_prec, -999999e100),
            Float::with_val(work_prec, -999999e-100),
        ];
        #[cfg(feature = "integer")]
        let z = [
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        #[cfg(feature = "rational")]
        let q = [
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];
        let u = [0, 1, 1000, u32::MAX];
        let s = [i32::MIN, -1000, -1, 0, 1, 1000, i32::MAX];
        let double = [
            f64::INFINITY,
            f64::MAX,
            f64::MIN_POSITIVE,
            0.0,
            -0.0,
            -f64::MIN_POSITIVE,
            f64::MIN,
            f64::NEG_INFINITY,
            f64::NAN,
            1.0,
            2.0,
            12.0e43,
        ];
        let single = [
            f32::INFINITY,
            f32::MAX,
            f32::MIN_POSITIVE,
            0.0,
            -0.0,
            -f32::MIN_POSITIVE,
            f32::MIN,
            f32::NEG_INFINITY,
            f32::NAN,
            1.0,
            2.0,
            12.0e30,
        ];
        #[cfg(feature = "integer")]
        for oo in &z {
            let of = Float::with_val(check_prec, oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
        #[cfg(feature = "rational")]
        for oo in &q {
            let of = Float::with_val(check_prec, oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
        for oo in &u {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
        for oo in &s {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
        for oo in &double {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
        for oo in &single {
            let of = Float::with_val(check_prec, *oo);
            for ff in &f {
                assert_eq!(ff.eq(oo), ff.eq(&of));
                assert_eq!(oo.eq(ff), of.eq(ff));
                assert_eq!(ff.eq(oo), oo.eq(ff));
                assert_eq!(ff.partial_cmp(oo), ff.partial_cmp(&of));
                assert_eq!(oo.partial_cmp(ff), of.partial_cmp(ff));
                assert_eq!(
                    ff.partial_cmp(oo),
                    oo.partial_cmp(ff).map(|o| o.reverse())
                );
            }
        }
    }
}
