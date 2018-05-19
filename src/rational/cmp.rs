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

use cast::cast;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::Inner;
use misc::NegAbs;
use std::cmp::Ordering;
use std::i32;
use {Integer, Rational};

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

macro_rules! cmp_rev {
    ($T:ty) => {
        impl PartialEq<Rational> for $T {
            #[inline]
            fn eq(&self, other: &Rational) -> bool {
                <Rational as PartialEq<$T>>::eq(other, self)
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

macro_rules! cmp_num {
    ($cmp:path; $($Num:ty)*) => { $(
        impl PartialEq<$Num> for Rational {
            #[inline]
            fn eq(&self, other: &$Num) -> bool {
                unsafe { $cmp(self.inner(), cast(*other), 1) == 0 }
            }
        }
        impl PartialOrd<$Num> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$Num) -> Option<Ordering> {
                let ord = unsafe { $cmp(self.inner(), cast(*other), 1) };
                Some(ord.cmp(&0))
            }
        }
        cmp_rev!{ $Num }
    )* };
}

cmp_num! { gmp::mpq_cmp_si; i8 i16 i32}
cmp_num! { xgmp::mpq_cmp_i64; i64 }
#[cfg(target_pointer_width = "32")]
cmp_num! { gmp::mpq_cmp_si; isize }
#[cfg(target_pointer_width = "64")]
cmp_num! { xgmp::mpq_cmp_i64; isize }
#[cfg(int_128)]
cmp_num! { xgmp::mpq_cmp_i128; i128 }

cmp_num! { gmp::mpq_cmp_ui; u8 u16 u32}
cmp_num! { xgmp::mpq_cmp_u64; u64 }
#[cfg(target_pointer_width = "32")]
cmp_num! { gmp::mpq_cmp_ui; usize }
#[cfg(target_pointer_width = "64")]
cmp_num! { xgmp::mpq_cmp_u64; usize }
#[cfg(int_128)]
cmp_num! { xgmp::mpq_cmp_u128; u128 }

macro_rules! cmp_num_iden {
    ($func:path; $Num:ty; $($Den:ty)*) => { $(
        impl PartialEq<($Num, $Den)> for Rational {
            #[inline]
            fn eq(&self, other: &($Num, $Den)) -> bool {
                assert_ne!(other.1, 0, "division by zero");
                let (neg_den, abs_den) = other.1.neg_abs();
                let as_neg;
                let to_compare = if neg_den {
                    as_neg = self.as_neg();
                    &*as_neg
                } else {
                    self
                };
                unsafe {
                    $func(to_compare.inner(), cast(other.0), cast(abs_den)) == 0
                }
            }
        }
        impl PartialOrd<($Num, $Den)> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &($Num, $Den)) -> Option<Ordering> {
                assert_ne!(other.1, 0, "division by zero");
                let (neg_den, abs_den) = other.1.neg_abs();
                let as_neg;
                let to_compare = if neg_den {
                    as_neg = self.as_neg();
                    &*as_neg
                } else {
                    self
                };
                let cmp = unsafe {
                    $func(to_compare.inner(), cast(other.0), cast(abs_den))
                };
                if neg_den {
                    Some(0.cmp(&cmp))
                } else {
                    Some(cmp.cmp(&0))
                }
            }
        }
        cmp_rev!{ ($Num, $Den) }
    )* };
}

macro_rules! cmp_num_uden {
    ($func:path; $Num:ty; $($Den:ty)*) => { $(
        impl PartialEq<($Num, $Den)> for Rational {
            #[inline]
            fn eq(&self, other: &($Num, $Den)) -> bool {
                assert_ne!(other.1, 0, "division by zero");
                unsafe {
                    $func(self.inner(), cast(other.0), cast(other.1)) == 0
                }
            }
        }
        impl PartialOrd<($Num, $Den)> for Rational {
            fn partial_cmp(&self, other: &($Num, $Den)) -> Option<Ordering> {
                assert_ne!(other.1, 0, "division by zero");
                let cmp = unsafe {
                    $func(self.inner(), cast(other.0), cast(other.1))
                };
                Some(cmp.cmp(&0))
            }
        }
        cmp_rev!{ ($Num, $Den) }
    )* };
}

macro_rules! cmp_inum_32 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { gmp::mpq_cmp_si; $Num; i8 i16 i32 }
        cmp_num_iden! { xgmp::mpq_cmp_i64; $Num; i64 }
        #[cfg(target_pointer_width = "32")]
        cmp_num_iden! { gmp::mpq_cmp_si; $Num; isize }
        #[cfg(target_pointer_width = "64")]
        cmp_num_iden! { xgmp::mpq_cmp_i64; $Num; isize }
        #[cfg(int_128)]
        cmp_num_iden! { xgmp::mpq_cmp_i128; $Num; i128 }

        cmp_num_uden! { gmp::mpq_cmp_si; $Num; u8 u16 u32 }
        cmp_num_uden! { xgmp::mpq_cmp_i64; $Num; u64 }
        #[cfg(target_pointer_width = "32")]
        cmp_num_uden! { gmp::mpq_cmp_si; $Num; usize }
        #[cfg(target_pointer_width = "64")]
        cmp_num_uden! { xgmp::mpq_cmp_i64; $Num; usize }
        #[cfg(int_128)]
        cmp_num_uden! { xgmp::mpq_cmp_i128; $Num; u128 }
    )* };
}

macro_rules! cmp_inum_64 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { xgmp::mpq_cmp_i64; $Num; i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        cmp_num_iden! { xgmp::mpq_cmp_i128; $Num; i128 }
        cmp_num_uden! { xgmp::mpq_cmp_i64; $Num; u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        cmp_num_uden! { xgmp::mpq_cmp_i128; $Num; u128 }
    )* };
}

#[cfg(int_128)]
macro_rules! cmp_inum_128 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { xgmp::mpq_cmp_i128; $Num; i8 i16 i32 i64 isize i128 }
        cmp_num_uden! { xgmp::mpq_cmp_i128; $Num; u8 u16 u32 u64 usize u128 }
    )* };
}

macro_rules! cmp_unum_32 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { gmp::mpq_cmp_ui; $Num; i8 i16 i32 }
        cmp_num_iden! { xgmp::mpq_cmp_u64; $Num; i64 }
        #[cfg(target_pointer_width = "32")]
        cmp_num_iden! { gmp::mpq_cmp_ui; $Num; isize }
        #[cfg(target_pointer_width = "64")]
        cmp_num_iden! { xgmp::mpq_cmp_u64; $Num; isize }
        #[cfg(int_128)]
        cmp_num_iden! { xgmp::mpq_cmp_u128; $Num; i128 }

        cmp_num_uden! { gmp::mpq_cmp_ui; $Num; u8 u16 u32 }
        cmp_num_uden! { xgmp::mpq_cmp_u64; $Num; u64 }
        #[cfg(target_pointer_width = "32")]
        cmp_num_uden! { gmp::mpq_cmp_ui; $Num; usize }
        #[cfg(target_pointer_width = "64")]
        cmp_num_uden! { xgmp::mpq_cmp_u64; $Num; usize }
        #[cfg(int_128)]
        cmp_num_uden! { xgmp::mpq_cmp_u128; $Num; u128 }
    )* };
}

macro_rules! cmp_unum_64 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { xgmp::mpq_cmp_u64; $Num; i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        cmp_num_iden! { xgmp::mpq_cmp_u128; $Num; i128 }
        cmp_num_uden! { xgmp::mpq_cmp_u64; $Num; u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        cmp_num_uden! { xgmp::mpq_cmp_u128; $Num; u128 }
    )* };
}

#[cfg(int_128)]
macro_rules! cmp_unum_128 {
    ($($Num:ty)*) => { $(
        cmp_num_iden! { xgmp::mpq_cmp_u128; $Num; i8 i16 i32 i64 isize i128 }
        cmp_num_uden! { xgmp::mpq_cmp_u128; $Num; u8 u16 u32 u64 usize u128 }
    )* };
}

cmp_inum_32! { i8 i16 i32 }
cmp_inum_64! { i64 }
#[cfg(target_pointer_width = "32")]
cmp_inum_32! { isize }
#[cfg(target_pointer_width = "64")]
cmp_inum_64! { isize }
#[cfg(int_128)]
cmp_inum_128! { i128 }

cmp_unum_32! { u8 u16 u32 }
cmp_unum_64! { u64 }
#[cfg(target_pointer_width = "32")]
cmp_unum_32! { usize }
#[cfg(target_pointer_width = "64")]
cmp_unum_64! { usize }
#[cfg(int_128)]
cmp_unum_128! { u128 }

macro_rules! cmp_f {
    ($($T:ty)*) => { $(
        impl PartialEq<$T> for Rational {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                other.is_finite() && unsafe {
                    xgmp::mpq_cmp_finite_d(self.inner(), cast(*other)) == 0
                }
            }
        }
        impl PartialOrd<$T> for Rational {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                if other.is_finite() {
                    let ord = unsafe {
                        xgmp::mpq_cmp_finite_d(self.inner(), cast(*other))
                    };
                    Some(ord.cmp(&0))
                } else if other.is_nan() {
                    None
                } else if other.is_sign_negative() {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
        }
        cmp_rev! { $T }
    )* };
}

cmp_f! { f32 f64 }

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use std::ops::Neg;
    use std::ops::Sub;
    use std::{f32, f64};
    #[cfg(int_128)]
    use tests::{I128, U128};
    use tests::{I32, I64, U32, U64};
    use Rational;

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
        let large = [(5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against = large
            .iter()
            .map(|&(n, d, s)| Rational::from((n, d)) << s)
            .chain(U32.iter().map(|&x| Rational::from(x)))
            .chain(I32.iter().map(|&x| Rational::from(x)))
            .chain(U64.iter().map(|&x| Rational::from(x)))
            .chain(I64.iter().map(|&x| Rational::from(x)))
            .collect::<Vec<Rational>>();
        #[cfg(int_128)]
        let mut against = against;
        #[cfg(int_128)]
        {
            against.extend(U128.iter().map(|&x| Rational::from(x)));
            against.extend(I128.iter().map(|&x| Rational::from(x)));
            check_cmp_prim(U128, &against);
            check_cmp_prim(I128, &against);
        }
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
        let large = [(5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against = large
            .iter()
            .map(|&(n, d, s)| Rational::from((n, d)) << s)
            .chain(U32.iter().map(|&x| Rational::from(x)))
            .chain(I32.iter().map(|&x| Rational::from(x)))
            .chain(U64.iter().map(|&x| Rational::from(x)))
            .chain(I64.iter().map(|&x| Rational::from(x)))
            .collect::<Vec<Rational>>();
        #[cfg(int_128)]
        let mut against = against;
        #[cfg(int_128)]
        {
            against.extend(U128.iter().map(|&x| Rational::from(x)));
            against.extend(I128.iter().map(|&x| Rational::from(x)));
            check_cmp_prim_tuple(U128, U128, &against);
            check_cmp_prim_tuple(U128, I128, &against);
            check_cmp_prim_tuple(I128, U128, &against);
            check_cmp_prim_tuple(I128, I128, &against);
        }
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

    #[test]
    fn check_cmp_f() {
        let large = [(5, 2, 0), (5, 17, 100), (-11, 3, 200), (33, 777, -150)];
        let against = large
            .iter()
            .map(|&(n, d, s)| Rational::from((n, d)) << s)
            .chain(U32.iter().map(|&x| Rational::from(x)))
            .chain(I32.iter().map(|&x| Rational::from(x)))
            .chain(U64.iter().map(|&x| Rational::from(x)))
            .chain(I64.iter().map(|&x| Rational::from(x)))
            .collect::<Vec<Rational>>();
        #[cfg(int_128)]
        let mut against = against;
        #[cfg(int_128)]
        {
            against.extend(U128.iter().map(|&x| Rational::from(x)));
            against.extend(I128.iter().map(|&x| Rational::from(x)));
        }
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
