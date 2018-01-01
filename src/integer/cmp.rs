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

use Integer;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp;
use inner::Inner;
use std::cmp::Ordering;

impl Eq for Integer {}

impl Ord for Integer {
    #[inline]
    fn cmp(&self, other: &Integer) -> Ordering {
        let ord = unsafe { gmp::mpz_cmp(self.inner(), other.inner()) };
        ord.cmp(&0)
    }
}

impl PartialEq for Integer {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        <Integer as Ord>::cmp(self, other) == Ordering::Equal
    }
}

impl PartialOrd for Integer {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        Some(<Integer as Ord>::cmp(self, other))
    }
}

macro_rules! cmp {
    { $T:ty, $func:path } => {
        impl PartialEq<$T> for Integer {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                <Integer as PartialOrd<$T>>::partial_cmp(self, other)
                    == Some(Ordering::Equal)
            }
        }

        impl PartialEq<Integer> for $T {
            #[inline]
            fn eq(&self, other: &Integer) -> bool {
                <Integer as PartialOrd<$T>>::partial_cmp(other, self)
                    == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$T> for Integer {
            #[inline]
            fn partial_cmp(&self, other: &$T) -> Option<Ordering> {
                let ord = unsafe { $func(self.inner(), (*other).into()) };
                Some(ord.cmp(&0))
            }
        }

        impl PartialOrd<Integer> for $T {
            #[inline]
            fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
                <Integer as PartialOrd<$T>>::partial_cmp(other, self)
                    .map(Ordering::reverse)
            }
        }
    };
}

macro_rules! cmp_cast {
    { $New:ty, $Existing:ty } => {
        impl PartialEq<$New> for Integer {
            #[inline]
            fn eq(&self, other: &$New) -> bool {
                <Integer as PartialOrd<$Existing>>::partial_cmp(
                    self,
                    &(*other as $Existing),
                ) == Some(Ordering::Equal)
            }
        }

        impl PartialEq<Integer> for $New {
            #[inline]
            fn eq(&self, other: &Integer) -> bool {
                <Integer as PartialOrd<$Existing>>::partial_cmp(
                    other,
                    &(*self as $Existing),
                ) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$New> for Integer {
            #[inline]
            fn partial_cmp(&self, other: &$New) -> Option<Ordering> {
                <Integer as PartialOrd<$Existing>>::partial_cmp(
                    self,
                    &(*other as $Existing),
                )
            }
        }

        impl PartialOrd<Integer> for $New {
            #[inline]
            fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
                <Integer as PartialOrd<$Existing>>::partial_cmp(
                    other,
                    &(*self as $Existing),
                ).map(Ordering::reverse)
            }
        }
    }
}

cmp_cast! { i8, i32 }
cmp_cast! { i16, i32 }
cmp! { i32, xgmp::mpz_cmp_i32 }
cmp! { i64, xgmp::mpz_cmp_i64 }
#[cfg(target_pointer_width = "32")]
cmp_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
cmp_cast! { isize, i64 }

cmp_cast! { u8, u32 }
cmp_cast! { u16, u32 }
cmp! { u32, xgmp::mpz_cmp_u32 }
cmp! { u64, xgmp::mpz_cmp_u64 }
#[cfg(target_pointer_width = "32")]
cmp_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
cmp_cast! { usize, u64 }

cmp_cast! { f32, f64 }

impl PartialEq<f64> for Integer {
    #[inline]
    fn eq(&self, other: &f64) -> bool {
        <Integer as PartialOrd<f64>>::partial_cmp(self, other)
            == Some(Ordering::Equal)
    }
}

impl PartialEq<Integer> for f64 {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        <Integer as PartialOrd<f64>>::partial_cmp(other, self)
            == Some(Ordering::Equal)
    }
}

impl PartialOrd<f64> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if other.is_nan() {
            None
        } else {
            let ord = unsafe { gmp::mpz_cmp_d(self.inner(), *other) };
            Some(ord.cmp(&0))
        }
    }
}

impl PartialOrd<Integer> for f64 {
    #[inline]
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        <Integer as PartialOrd<f64>>::partial_cmp(other, self)
            .map(Ordering::reverse)
    }
}
