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

use {Integer, Rational};
#[cfg(feature = "float")]
use Float;
use cast::cast;
use ext::gmp as xgmp;
#[cfg(feature = "float")]
use float::SmallFloat;
use gmp_mpfr_sys::gmp;
use inner::Inner;
use misc::NegAbs;
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
        Some(<Rational as Ord>::cmp(self, other))
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
        <Rational as PartialEq<Integer>>::eq(other, self)
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
        <Rational as PartialOrd<Integer>>::partial_cmp(other, self)
            .map(Ordering::reverse)
    }
}

macro_rules! cmp {
    ($T: ty, $cmp: path) => {
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                unsafe { $cmp(self.inner(), cast(*other), 1) == 0 }
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
                let ord = unsafe { $cmp(self.inner(), cast(*other), 1) };
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
    };
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
    ($func: path; $Num: ty; $Den: ty) => {
        impl PartialEq<($Num, $Den)> for Rational {
            fn eq(&self, other: &($Num, $Den)) -> bool {
                assert_ne!(other.1, 0, "division by zero");
                let neg = self.cmp0() == Ordering::Less;
                let (neg_num, abs_num) = other.0.neg_abs();
                let (neg_den, abs_den) = other.1.neg_abs();
                let as_neg;
                let abs = if neg {
                    if abs_num == 0 || neg_num == neg_den {
                        return false;
                    }
                    as_neg = self.as_neg();
                    &*as_neg
                } else {
                    if abs_num != 0 && neg_num != neg_den {
                        return false;
                    }
                    &self
                };
                unsafe {
                    $func(abs.inner(), cast(abs_num), cast(abs_den)) == 0
                }
            }
        }
        impl PartialEq<Rational> for ($Num, $Den) {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                <Rational as PartialEq<($Num, $Den)>>::eq(other, self)
            }
        }
        impl PartialOrd<($Num, $Den)> for Rational {
            fn partial_cmp(&self, other: &($Num, $Den)) -> Option<Ordering> {
                assert_ne!(other.1, 0, "division by zero");
                let neg = self.cmp0() == Ordering::Less;
                let (neg_num, abs_num) = other.0.neg_abs();
                let (neg_den, abs_den) = other.1.neg_abs();
                let as_neg;
                let abs = if neg {
                    if abs_num == 0 || neg_num == neg_den {
                        return Some(Ordering::Less);
                    }
                    as_neg = self.as_neg();
                    &*as_neg
                } else {
                    if abs_num != 0 && neg_num != neg_den {
                        return Some(Ordering::Greater);
                    }
                    &self
                };
                let cmp_abs =
                    unsafe { $func(abs.inner(), cast(abs_num), cast(abs_den)) };
                let cmp = if neg { -cmp_abs } else { cmp_abs };
                Some(cmp.cmp(&0))
            }
        }
        impl PartialOrd<Rational> for ($Num, $Den) {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                <Rational as PartialOrd<($Num, $Den)>>::partial_cmp(other, self)
                    .map(Ordering::reverse)
            }
        }
    };
}

// (Major, Major), (Major, Minor*), (Minor*, Major)
macro_rules! matrix {
    ($func: path; $Major: ty $(; $Minor: ty)*) => {
        cross! { $func; $Major; $Major }
        $(cross! { $func; $Major; $Minor })*
        $(cross! { $func; $Minor; $Major })*
    };
}

matrix! { xgmp::mpq_cmp_u32; u8 }
matrix! { xgmp::mpq_cmp_u32; i8; u8 }
matrix! { xgmp::mpq_cmp_u32; u16; i8; u8 }
matrix! { xgmp::mpq_cmp_u32; i16; u16; i8; u8 }
matrix! { xgmp::mpq_cmp_u32; u32; i16; u16; i8; u8 }
matrix! { xgmp::mpq_cmp_u32; i32; u32; i16; u16; i8; u8 }
#[cfg(target_pointer_width = "32")]
matrix! { xgmp::mpq_cmp_u32; usize; i32; u32; i16; u16; i8; u8 }
#[cfg(target_pointer_width = "32")]
matrix! { xgmp::mpq_cmp_u32; isize; usize; i32; u32; i16; u16; i8; u8 }
#[cfg(target_pointer_width = "64")]
matrix! { xgmp::mpq_cmp_u64; usize; i32; u32; i16; u16; i8; u8 }
#[cfg(target_pointer_width = "64")]
matrix! { xgmp::mpq_cmp_u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! { xgmp::mpq_cmp_u64; u64; isize; usize; i32; u32; i16; u16; i8; u8 }
matrix! {
    xgmp::mpq_cmp_u64; i64; u64; isize; usize; i32; u32; i16; u16; i8; u8
}

#[cfg(feature = "float")]
macro_rules! cmp_f {
    ($T: ty) => {
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                <Float as PartialOrd<Rational>>::partial_cmp(
                    &*SmallFloat::from(*other),
                    self,
                ) == Some(Ordering::Equal)
            }
        }

        impl PartialEq<Rational> for $T {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                <Float as PartialOrd<Rational>>::partial_cmp(
                    &*SmallFloat::from(*self),
                    other,
                ) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                <Float as PartialOrd<Rational>>::partial_cmp(
                    &*SmallFloat::from(*other),
                    self,
                ).map(Ordering::reverse)
            }
        }

        impl PartialOrd<Rational> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                <Float as PartialOrd<Rational>>::partial_cmp(
                    &*SmallFloat::from(*self),
                    other,
                )
            }
        }
    };
}

#[cfg(feature = "float")]
cmp_f! { f32 }
#[cfg(feature = "float")]
cmp_f! { f64 }

#[cfg(test)]
mod tests {
    use Rational;
    #[cfg(feature = "float")]
    use std::{f32, f64};
    #[cfg(feature = "float")]
    use std::cmp::Ordering;
    #[cfg(feature = "float")]
    use std::ops::Neg;
    use std::ops::Sub;
    use tests::{I32, I64, U32, U64};

    fn check_cmp_prim<T>(s: &[T], against: &[Rational])
    where
        Rational: From<T> + PartialEq<T> + PartialOrd<T>,
        T: Copy + PartialEq<Rational> + PartialOrd<Rational>,
    {
        for op in s {
            let iop = Rational::from(*op);
            for b in against {
                assert_eq!(b.eq(op), <Rational as PartialEq>::eq(&b, &iop));
                assert_eq!(op.eq(&b), <Rational as PartialEq>::eq(&iop, &b));
                assert_eq!(b.eq(op), op.eq(&b));
                assert_eq!(
                    b.partial_cmp(op),
                    <Rational as PartialOrd>::partial_cmp(&b, &iop)
                );
                assert_eq!(
                    op.partial_cmp(&b),
                    <Rational as PartialOrd>::partial_cmp(&iop, &b)
                );
                assert_eq!(
                    b.partial_cmp(op).unwrap(),
                    op.partial_cmp(&b).unwrap().reverse()
                );
            }
        }
    }

    #[test]
    fn check_cmp_u_s() {
        let large = &[(5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against =
            (large.iter().map(|&(n, d, s)| Rational::from((n, d)) << s))
                .chain(U32.iter().map(|&x| Rational::from(x)))
                .chain(I32.iter().map(|&x| Rational::from(x)))
                .chain(U64.iter().map(|&x| Rational::from(x)))
                .chain(I64.iter().map(|&x| Rational::from(x)))
                .collect::<Vec<Rational>>();
        check_cmp_prim(U32, &against);
        check_cmp_prim(I32, &against);
        check_cmp_prim(U64, &against);
        check_cmp_prim(I64, &against);
    }

    fn check_cmp_prim_tuple<N, D>(num: &[N], den: &[D], against: &[Rational])
    where
        Rational: From<(N, D)> + PartialEq<(N, D)> + PartialOrd<(N, D)>,
        N: Copy,
        D: Copy + Eq + Sub<Output = D>,
        (N, D): PartialEq<Rational> + PartialOrd<Rational>,
    {
        for n in num {
            for d in den {
                if *d == *d - *d {
                    continue;
                }
                let op = (*n, *d);
                let iop = Rational::from(op);
                for b in against {
                    assert_eq!(
                        b.eq(&op),
                        <Rational as PartialEq>::eq(&b, &iop)
                    );
                    assert_eq!(
                        op.eq(&b),
                        <Rational as PartialEq>::eq(&iop, &b)
                    );
                    assert_eq!(b.eq(&op), op.eq(&b));
                    assert_eq!(
                        b.partial_cmp(&op),
                        <Rational as PartialOrd>::partial_cmp(&b, &iop)
                    );
                    assert_eq!(
                        op.partial_cmp(&b),
                        <Rational as PartialOrd>::partial_cmp(&iop, &b)
                    );
                    assert_eq!(
                        b.partial_cmp(&op).unwrap(),
                        op.partial_cmp(&b).unwrap().reverse()
                    );
                }
            }
        }
    }

    #[test]
    fn check_cmp_tuple() {
        let large = &[(5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against =
            (large.iter().map(|&(n, d, s)| Rational::from((n, d)) << s))
                .chain(U32.iter().map(|&x| Rational::from(x)))
                .chain(I32.iter().map(|&x| Rational::from(x)))
                .chain(U64.iter().map(|&x| Rational::from(x)))
                .chain(I64.iter().map(|&x| Rational::from(x)))
                .collect::<Vec<Rational>>();
        check_cmp_prim_tuple(U32, U32, &against);
        check_cmp_prim_tuple(U32, I32, &against);
        check_cmp_prim_tuple(U32, U64, &against);
        check_cmp_prim_tuple(U32, I64, &against);
        check_cmp_prim_tuple(I32, U32, &against);
        check_cmp_prim_tuple(I32, I32, &against);
        check_cmp_prim_tuple(I32, U64, &against);
        check_cmp_prim_tuple(I32, I64, &against);
        check_cmp_prim_tuple(U64, U32, &against);
        check_cmp_prim_tuple(U64, I32, &against);
        check_cmp_prim_tuple(U64, U64, &against);
        check_cmp_prim_tuple(U64, I64, &against);
        check_cmp_prim_tuple(I64, U32, &against);
        check_cmp_prim_tuple(I64, I32, &against);
        check_cmp_prim_tuple(I64, U64, &against);
        check_cmp_prim_tuple(I64, I64, &against);
    }

    #[cfg(feature = "float")]
    fn check_known_cmp<T>(t: T, against: &Rational, ord: Ordering)
    where
        Rational: PartialEq<T> + PartialEq<<T as Neg>::Output>,
        Rational: PartialOrd<T> + PartialOrd<<T as Neg>::Output>,
        T: Copy + Neg + PartialEq<Rational> + PartialOrd<Rational>,
        <T as Neg>::Output: PartialEq<Rational> + PartialOrd<Rational>,
    {
        let neg = against.as_neg();
        assert_eq!(t.eq(against), ord == Ordering::Equal);
        assert_eq!((-t).eq(&*neg), ord == Ordering::Equal);
        assert_eq!(against.eq(&t), ord == Ordering::Equal);
        assert_eq!(neg.eq(&-t), ord == Ordering::Equal);
        assert_eq!(t.partial_cmp(against), Some(ord));
        assert_eq!((-t).partial_cmp(&*neg), Some(ord.reverse()));
        assert_eq!(against.partial_cmp(&t), Some(ord.reverse()));
        assert_eq!(neg.partial_cmp(&-t), Some(ord));
    }

    #[cfg(feature = "float")]
    fn check_nan_cmp<T>(t: T, against: &Rational)
    where
        Rational: PartialEq<T> + PartialEq<<T as Neg>::Output>,
        Rational: PartialOrd<T> + PartialOrd<<T as Neg>::Output>,
        T: Copy + Neg + PartialEq<Rational> + PartialOrd<Rational>,
        <T as Neg>::Output: PartialEq<Rational> + PartialOrd<Rational>,
    {
        let neg = against.as_neg();
        assert!(t.ne(against));
        assert!((-t).ne(&*neg));
        assert!(against.ne(&t));
        assert!(neg.ne(&-t));
        assert!(t.partial_cmp(against).is_none());
        assert!((-t).partial_cmp(&*neg).is_none());
        assert!(against.partial_cmp(&t).is_none());
        assert!(neg.partial_cmp(&-t).is_none());
    }

    #[cfg(feature = "float")]
    #[test]
    fn check_cmp_f() {
        let large = &[(5, 2, 0), (5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against =
            (large.iter().map(|&(n, d, s)| Rational::from((n, d)) << s))
                .chain(U32.iter().map(|&x| Rational::from(x)))
                .chain(I32.iter().map(|&x| Rational::from(x)))
                .chain(U64.iter().map(|&x| Rational::from(x)))
                .chain(I64.iter().map(|&x| Rational::from(x)))
                .collect::<Vec<Rational>>();
        for b in &against {
            check_known_cmp(0.0f32, b, b.cmp0().reverse());
            check_known_cmp(0.0f64, b, b.cmp0().reverse());
            let ord = 5.partial_cmp(&(b.clone() << 1)).unwrap();
            check_known_cmp(2.5f32, b, ord);
            check_known_cmp(2.5f64, b, ord);
            check_known_cmp(f32::INFINITY, b, Ordering::Greater);
            check_known_cmp(f64::INFINITY, b, Ordering::Greater);
            check_nan_cmp(f32::NAN, b);
            check_nan_cmp(f64::NAN, b);
        }
    }
}
