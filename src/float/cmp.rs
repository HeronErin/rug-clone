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
    use {Assign, Float};
    #[cfg(feature = "integer")]
    use Integer;
    #[cfg(feature = "rational")]
    use Rational;
    use float::Special;
    #[cfg(feature = "integer")]
    use std::str::FromStr;

    fn check_cmp_prim<T>(s: &[T], against: &[Float])
    where
        Float: Assign<T> + PartialEq<T> + PartialOrd<T>,
        T: Copy + PartialEq<Float> + PartialOrd<Float>,
    {
        for op in s {
            let fop = Float::with_val(100, *op);
            for b in against {
                assert_eq!(b.eq(op), <Float as PartialEq>::eq(&b, &fop));
                assert_eq!(op.eq(&b), <Float as PartialEq>::eq(&fop, &b));
                assert_eq!(b.eq(op), op.eq(&b));
                assert_eq!(
                    b.partial_cmp(op),
                    <Float as PartialOrd>::partial_cmp(&b, &fop)
                );
                assert_eq!(
                    op.partial_cmp(&b),
                    <Float as PartialOrd>::partial_cmp(&fop, &b)
                );
                assert_eq!(
                    b.partial_cmp(op),
                    op.partial_cmp(&b).map(|o| o.reverse())
                );
            }
        }
    }

    #[cfg(feature = "integer")]
    fn check_cmp_big<'a, T>(s: &'a [T], against: &[Float])
    where
        Float: Assign<&'a T> + PartialEq<T> + PartialOrd<T>,
        T: PartialEq<Float> + PartialOrd<Float>,
    {
        for op in s {
            let fop = Float::with_val(100, op);
            for b in against {
                assert_eq!(b.eq(op), <Float as PartialEq>::eq(&b, &fop));
                assert_eq!(op.eq(&b), <Float as PartialEq>::eq(&fop, &b));
                assert_eq!(b.eq(op), op.eq(&b));
                assert_eq!(
                    b.partial_cmp(op),
                    <Float as PartialOrd>::partial_cmp(&b, &fop)
                );
                assert_eq!(
                    op.partial_cmp(&b),
                    <Float as PartialOrd>::partial_cmp(&fop, &b)
                );
                assert_eq!(
                    b.partial_cmp(op),
                    op.partial_cmp(&b).map(|o| o.reverse())
                );
            }
        }
    }

    #[test]
    fn check_cmp_others() {
        use tests::{U32, I32, U64, I64, F32, F64};
        let large = &[
            Float::with_val(20, Special::Zero),
            Float::with_val(20, Special::NegZero),
            Float::with_val(20, Special::Infinity),
            Float::with_val(20, Special::NegInfinity),
            Float::with_val(20, Special::Nan),
            Float::with_val(20, 1),
            Float::with_val(20, -1),
            Float::with_val(20, 999999e100),
            Float::with_val(20, 999999e-100),
            Float::with_val(20, -999999e100),
            Float::with_val(20, -999999e-100),
        ];
        #[cfg(feature = "integer")]
        let z = &[
            Integer::from(0),
            Integer::from(1),
            Integer::from(-1),
            Integer::from_str("-1000000000000").unwrap(),
            Integer::from_str("1000000000000").unwrap(),
        ];
        #[cfg(feature = "rational")]
        let q = &[
            Rational::from(0),
            Rational::from(1),
            Rational::from(-1),
            Rational::from_str("-1000000000000/33333333333").unwrap(),
            Rational::from_str("1000000000000/33333333333").unwrap(),
        ];

        let against = (large.iter().cloned())
            .chain(U32.iter().map(|&x| Float::with_val(20, x)))
            .chain(I32.iter().map(|&x| Float::with_val(20, x)))
            .chain(U64.iter().map(|&x| Float::with_val(20, x)))
            .chain(I64.iter().map(|&x| Float::with_val(20, x)))
            .chain(F32.iter().map(|&x| Float::with_val(20, x)))
            .chain(F64.iter().map(|&x| Float::with_val(20, x)))
            .collect::<Vec<Float>>();
        #[cfg(feature = "integer")]
        let mut against = against;
        #[cfg(feature = "integer")]
        against.extend(z.iter().map(|x| Float::with_val(20, x)));
        #[cfg(feature = "rational")]
        against.extend(q.iter().map(|x| Float::with_val(20, x)));
        check_cmp_prim(U32, &against);
        check_cmp_prim(I32, &against);
        check_cmp_prim(U64, &against);
        check_cmp_prim(I64, &against);
        check_cmp_prim(F32, &against);
        check_cmp_prim(F64, &against);
        #[cfg(feature = "integer")]
        check_cmp_big(z, &against);
        #[cfg(feature = "rational")]
        check_cmp_big(q, &against);
    }
}
