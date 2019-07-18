// Copyright © 2016–2019 University of Malta

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
// this program. If not, see <https://www.gnu.org/licenses/>.

use crate::cast::CheckedCast;
use crate::ext::xmpz;
use crate::integer::SmallInteger;
use crate::ops::{
    DivRounding, DivRoundingAssign, DivRoundingFrom, RemRounding, RemRoundingAssign,
    RemRoundingFrom,
};
use crate::{Assign, Integer};
use std::os::raw::{c_long, c_ulong};

// big / big -> Big
// big / &big -> Big
// &big / big -> Big
// &big / &big -> Incomplete
// big /= big
// big /= &big
// big /-> big
// &big /-> big
// struct Incomplete
// Incomplete -> Big
// big = Incomplete
macro_rules! div_op {
    (
        $trunc_fn:path, $ceil_fn:path, $floor_fn:path, $euc_fn:path;
        $Imp:ident $trunc:ident $ceil:ident $floor:ident $euc:ident;
        $ImpAssign:ident
            $trunc_assign:ident $ceil_assign:ident $floor_assign:ident $euc_assign:ident;
        $ImpFrom:ident $trunc_from:ident $ceil_from:ident $floor_from:ident $euc_from:ident;
        $Incomplete:ident
    ) => {
        impl $Imp for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$trunc_assign(&mut self, &rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$ceil_assign(&mut self, &rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$floor_assign(&mut self, &rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$euc_assign(&mut self, &rhs);
                self
            }
        }

        impl $Imp<&Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: &Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$trunc_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: &Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$ceil_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: &Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$floor_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: &Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$euc_assign(&mut self, rhs);
                self
            }
        }

        impl $Imp<Integer> for &Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<&Integer>>::$trunc_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $ceil(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<&Integer>>::$ceil_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $floor(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<&Integer>>::$floor_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $euc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<&Integer>>::$euc_from(&mut rhs, self);
                rhs
            }
        }

        impl<'i> $Imp for &'i Integer {
            type Output = $Incomplete<'i>;
            #[inline]
            fn $trunc(self, rhs: &'i Integer) -> $Incomplete<'_> {
                $Incomplete::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'i Integer) -> $Incomplete<'_> {
                $Incomplete::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'i Integer) -> $Incomplete<'_> {
                $Incomplete::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'i Integer) -> $Incomplete<'_> {
                $Incomplete::Euc(self, rhs)
            }
        }

        impl $ImpAssign for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: Integer) {
                <Integer as $ImpAssign<&Integer>>::$trunc_assign(self, &rhs);
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: Integer) {
                <Integer as $ImpAssign<&Integer>>::$ceil_assign(self, &rhs);
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: Integer) {
                <Integer as $ImpAssign<&Integer>>::$floor_assign(self, &rhs);
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: Integer) {
                <Integer as $ImpAssign<&Integer>>::$euc_assign(self, &rhs);
            }
        }

        impl $ImpAssign<&Integer> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: &Integer) {
                $trunc_fn(self, None, Some(rhs));
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: &Integer) {
                $ceil_fn(self, None, Some(rhs));
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: &Integer) {
                $floor_fn(self, None, Some(rhs));
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: &Integer) {
                $euc_fn(self, None, Some(rhs));
            }
        }

        impl $ImpFrom for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: Integer) {
                <Integer as $ImpFrom<&Integer>>::$trunc_from(self, &lhs);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: Integer) {
                <Integer as $ImpFrom<&Integer>>::$ceil_from(self, &lhs);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: Integer) {
                <Integer as $ImpFrom<&Integer>>::$floor_from(self, &lhs);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: Integer) {
                <Integer as $ImpFrom<&Integer>>::$euc_from(self, &lhs);
            }
        }

        impl $ImpFrom<&Integer> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: &Integer) {
                $trunc_fn(self, Some(lhs), None);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: &Integer) {
                $ceil_fn(self, Some(lhs), None);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: &Integer) {
                $floor_fn(self, Some(lhs), None);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: &Integer) {
                $euc_fn(self, Some(lhs), None);
            }
        }

        #[derive(Debug)]
        pub enum $Incomplete<'i> {
            Trunc(&'i Integer, &'i Integer),
            Ceil(&'i Integer, &'i Integer),
            Floor(&'i Integer, &'i Integer),
            Euc(&'i Integer, &'i Integer),
        }

        impl Assign<$Incomplete<'_>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                match src {
                    $Incomplete::Trunc(lhs, rhs) => {
                        $trunc_fn(self, Some(lhs), Some(rhs));
                    }
                    $Incomplete::Ceil(lhs, rhs) => {
                        $ceil_fn(self, Some(lhs), Some(rhs));
                    }
                    $Incomplete::Floor(lhs, rhs) => {
                        $floor_fn(self, Some(lhs), Some(rhs));
                    }
                    $Incomplete::Euc(lhs, rhs) => {
                        $euc_fn(self, Some(lhs), Some(rhs));
                    }
                }
            }
        }

        impl From<$Incomplete<'_>> for Integer {
            #[inline]
            fn from(src: $Incomplete<'_>) -> Self {
                let mut dst = Integer::new();
                dst.assign(src);
                dst
            }
        }
    };
}

// big / prim -> Big
// big / &prim -> Big
// &big / prim -> Incomplete
// &big / &prim -> Incomplete
// big /= prim
// big /= &prim
// struct Incomplete
// Incomplete -> Big
// big = Incomplete
// prim / big -> Big
// prim / &big -> FromIncomplete
// &prim / big -> Big
// &prim / &big -> FromIncomplete
// prim /-> big
// &prim /-> big
// struct FromIncomplete
// FromIncomplete -> Big
// big = FromIncomplete
macro_rules! div_prim {
    (
        $trunc_fn:path, $ceil_fn:path, $floor_fn:path, $euc_fn:path;
        $trunc_from_fn:path, $ceil_from_fn:path, $floor_from_fn:path, $euc_from_fn:path;
        $Imp:ident $trunc:ident $ceil:ident $floor:ident $euc:ident;
        $ImpAssign:ident
            $trunc_assign:ident $ceil_assign:ident $floor_assign:ident $euc_assign:ident;
        $ImpFrom:ident $trunc_from:ident $ceil_from:ident $floor_from:ident $euc_from:ident;
        $($T:ty, $Incomplete:ident, $FromIncomplete:ident;)*
    ) => { $(
        impl $Imp<$T> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$trunc_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$ceil_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$floor_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$euc_assign(&mut self, rhs);
                self
            }
        }

        impl $Imp<&$T> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: &$T) -> Integer {
                <Integer as $ImpAssign<$T>>::$trunc_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: &$T) -> Integer {
                <Integer as $ImpAssign<$T>>::$ceil_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: &$T) -> Integer {
                <Integer as $ImpAssign<$T>>::$floor_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: &$T) -> Integer {
                <Integer as $ImpAssign<$T>>::$euc_assign(&mut self, *rhs);
                self
            }
        }

        impl<'i> $Imp<$T> for &'i Integer {
            type Output = $Incomplete<'i>;
            #[inline]
            fn $trunc(self, rhs: $T) -> $Incomplete<'i> {
                $Incomplete::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: $T) -> $Incomplete<'i> {
                $Incomplete::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: $T) -> $Incomplete<'i> {
                $Incomplete::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: $T) -> $Incomplete<'i> {
                $Incomplete::Euc(self, rhs)
            }
        }

        impl<'t, 'i> $Imp<&'t $T> for &'i Integer {
            type Output = $Incomplete<'i>;
            #[inline]
            fn $trunc(self, rhs: &$T) -> $Incomplete<'i> {
                <&Integer as $Imp<$T>>::$trunc(self, *rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &$T) -> $Incomplete<'i> {
                <&Integer as $Imp<$T>>::$ceil(self, *rhs)
            }
            #[inline]
            fn $floor(self, rhs: &$T) -> $Incomplete<'i> {
                <&Integer as $Imp<$T>>::$floor(self, *rhs)
            }
            #[inline]
            fn $euc(self, rhs: &$T) -> $Incomplete<'i> {
                <&Integer as $Imp<$T>>::$euc(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: $T) {
                $trunc_fn(self, None, rhs);
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: $T) {
                $ceil_fn(self, None, rhs);
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: $T) {
                $floor_fn(self, None, rhs);
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: $T) {
                $euc_fn(self, None, rhs);
            }
        }

        impl $ImpAssign<&$T> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: &$T) {
                <Integer as $ImpAssign<$T>>::$trunc_assign(self, *rhs);
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: &$T) {
                <Integer as $ImpAssign<$T>>::$ceil_assign(self, *rhs);
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: &$T) {
                <Integer as $ImpAssign<$T>>::$floor_assign(self, *rhs);
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: &$T) {
                <Integer as $ImpAssign<$T>>::$euc_assign(self, *rhs);
            }
        }

        #[derive(Debug)]
        pub enum $Incomplete<'i> {
            Trunc(&'i Integer, $T),
            Ceil(&'i Integer, $T),
            Floor(&'i Integer, $T),
            Euc(&'i Integer, $T),
        }

        impl Assign<$Incomplete<'_>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Incomplete<'_>) {
                match src {
                    $Incomplete::Trunc(lhs, rhs) => {
                        $trunc_fn(self, Some(lhs), rhs);
                    }
                    $Incomplete::Ceil(lhs, rhs) => {
                        $ceil_fn(self, Some(lhs), rhs);
                    }
                    $Incomplete::Floor(lhs, rhs) => {
                        $floor_fn(self, Some(lhs), rhs);
                    }
                    $Incomplete::Euc(lhs, rhs) => {
                        $euc_fn(self, Some(lhs), rhs);
                    }
                }
            }
        }

        impl From<$Incomplete<'_>> for Integer {
            #[inline]
            fn from(src: $Incomplete<'_>) -> Self {
                let mut dst = Integer::new();
                dst.assign(src);
                dst
            }
        }

        impl $Imp<Integer> for $T {
            type Output = Integer;
            #[inline]
            fn $trunc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$trunc_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $ceil(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$ceil_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $floor(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$floor_from(&mut rhs, self);
                rhs
            }
            #[inline]
            fn $euc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$euc_from(&mut rhs, self);
                rhs
            }
        }

        impl<'i> $Imp<&'i Integer> for $T {
            type Output = $FromIncomplete<'i>;
            #[inline]
            fn $trunc(self, rhs: &Integer) -> $FromIncomplete<'_> {
                $FromIncomplete::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &Integer) -> $FromIncomplete<'_> {
                $FromIncomplete::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &Integer) -> $FromIncomplete<'_> {
                $FromIncomplete::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &Integer) -> $FromIncomplete<'_> {
                $FromIncomplete::Euc(self, rhs)
            }
        }

        impl $Imp<Integer> for &$T {
            type Output = Integer;
            #[inline]
            fn $trunc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$trunc_from(&mut rhs, *self);
                rhs
            }
            #[inline]
            fn $ceil(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$ceil_from(&mut rhs, *self);
                rhs
            }
            #[inline]
            fn $floor(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$floor_from(&mut rhs, *self);
                rhs
            }
            #[inline]
            fn $euc(self, mut rhs: Integer) -> Integer {
                <Integer as $ImpFrom<$T>>::$euc_from(&mut rhs, *self);
                rhs
            }
        }

        impl<'i> $Imp<&'i Integer> for &$T {
            type Output = $FromIncomplete<'i>;
            #[inline]
            fn $trunc(self, rhs: &'i Integer) -> $FromIncomplete<'i> {
                <$T as $Imp<&Integer>>::$trunc(*self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'i Integer) -> $FromIncomplete<'i> {
                <$T as $Imp<&Integer>>::$ceil(*self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'i Integer) -> $FromIncomplete<'i> {
                <$T as $Imp<&Integer>>::$floor(*self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'i Integer) -> $FromIncomplete<'i> {
                <$T as $Imp<&Integer>>::$euc(*self, rhs)
            }
        }

        impl $ImpFrom<$T> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: $T) {
                $trunc_from_fn(self, lhs, None);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: $T) {
                $ceil_from_fn(self, lhs, None);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: $T) {
                $floor_from_fn(self, lhs, None);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: $T) {
                $euc_from_fn(self, lhs, None);
            }
        }

        impl $ImpFrom<&$T> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: &$T) {
                <Integer as $ImpFrom<$T>>::$trunc_from(self, *lhs);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: &$T) {
                <Integer as $ImpFrom<$T>>::$ceil_from(self, *lhs);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: &$T) {
                <Integer as $ImpFrom<$T>>::$floor_from(self, *lhs);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: &$T) {
                <Integer as $ImpFrom<$T>>::$euc_from(self, *lhs);
            }
        }

        #[derive(Debug)]
        pub enum $FromIncomplete<'i> {
            Trunc($T, &'i Integer),
            Ceil($T, &'i Integer),
            Floor($T, &'i Integer),
            Euc($T, &'i Integer),
        }

        impl Assign<$FromIncomplete<'_>> for Integer {
            #[inline]
            fn assign(&mut self, src: $FromIncomplete<'_>) {
                match src {
                    $FromIncomplete::Trunc(lhs, rhs) => {
                        $trunc_from_fn(self, lhs, Some(rhs));
                    }
                    $FromIncomplete::Ceil(lhs, rhs) => {
                        $ceil_from_fn(self, lhs, Some(rhs));
                    }
                    $FromIncomplete::Floor(lhs, rhs) => {
                        $floor_from_fn(self, lhs, Some(rhs));
                    }
                    $FromIncomplete::Euc(lhs, rhs) => {
                        $euc_from_fn(self, lhs, Some(rhs));
                    }
                }
            }
        }

        impl From<$FromIncomplete<'_>> for Integer {
            #[inline]
            fn from(src: $FromIncomplete<'_>) -> Self {
                let mut dst = Integer::new();
                dst.assign(src);
                dst
            }
        }
    )* };
}

div_op! {
    xmpz::tdiv_q, xmpz::cdiv_q, xmpz::fdiv_q, xmpz::ediv_q;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom div_trunc_from div_ceil_from div_floor_from div_euc_from;
    DivRoundingIncomplete
}
div_op! {
    xmpz::tdiv_r, xmpz::cdiv_r, xmpz::fdiv_r, xmpz::ediv_r;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    RemRoundingIncomplete
}

div_prim! {
    PrimOps::tdiv_q, PrimOps::cdiv_q, PrimOps::fdiv_q, PrimOps::ediv_q;
    PrimOps::tdiv_q_from, PrimOps::cdiv_q_from, PrimOps::fdiv_q_from, PrimOps::ediv_q_from;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom div_trunc_from div_ceil_from div_floor_from div_euc_from;
    i32, DivRoundingI32Incomplete, DivRoundingFromI32Incomplete;
    i64, DivRoundingI64Incomplete, DivRoundingFromI64Incomplete;
    u32, DivRoundingU32Incomplete, DivRoundingFromU32Incomplete;
    u64, DivRoundingU64Incomplete, DivRoundingFromU64Incomplete;
}
div_prim! {
    PrimOps::tdiv_r, PrimOps::cdiv_r, PrimOps::fdiv_r, PrimOps::ediv_r;
    PrimOps::tdiv_r_from, PrimOps::cdiv_r_from, PrimOps::fdiv_r_from, PrimOps::ediv_r_from;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    i32, RemRoundingI32Incomplete, RemRoundingFromI32Incomplete;
    i64, RemRoundingI64Incomplete, RemRoundingFromI64Incomplete;
    u32, RemRoundingU32Incomplete, RemRoundingFromU32Incomplete;
    u64, RemRoundingU64Incomplete, RemRoundingFromU64Incomplete;
}

trait PrimOps<Long>: AsLong {
    fn tdiv_q(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn cdiv_q(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn fdiv_q(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn ediv_q(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn tdiv_q_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn cdiv_q_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn fdiv_q_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn ediv_q_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn tdiv_r(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn cdiv_r(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn fdiv_r(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn ediv_r(rop: &mut Integer, op1: Option<&Integer>, op2: Self);
    fn tdiv_r_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn cdiv_r_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn fdiv_r_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
    fn ediv_r_from(rop: &mut Integer, op1: Self, op2: Option<&Integer>);
}

trait AsLong: Copy {
    type Long;
}

macro_rules! as_long {
    ($Long:ty: $($Prim:ty)*) => { $(
        impl AsLong for $Prim {
            type Long = $Long;
        }
    )* }
}

as_long! { c_long: i8 i16 i32 i64 i128 isize }
as_long! { c_ulong: u8 u16 u32 u64 u128 usize }

macro_rules! forward {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        fn $fn(rop: &mut Integer, op1: Option<&Integer>, op2: Self) {
            if let Some(op2) = op2.checked_cast() {
                $deleg_long(rop, op1, op2);
            } else {
                let small: SmallInteger = op2.into();
                $deleg(rop, op1, Some(&*small));
            }
        }
    };
}
macro_rules! reverse {
    (fn $fn:ident() -> $deleg_long:path, $deleg:path) => {
        #[inline]
        fn $fn(rop: &mut Integer, op1: Self, op2: Option<&Integer>) {
            if let Some(op1) = op1.checked_cast() {
                $deleg_long(rop, op1, op2);
            } else {
                let small: SmallInteger = op1.into();
                $deleg(rop, Some(&*small), op2);
            }
        }
    };
}

impl<T> PrimOps<c_long> for T
where
    T: AsLong<Long = c_long> + CheckedCast<c_long> + Into<SmallInteger>,
{
    forward! { fn tdiv_q() -> xmpz::tdiv_q_si, xmpz::tdiv_q }
    forward! { fn cdiv_q() -> xmpz::cdiv_q_si, xmpz::cdiv_q }
    forward! { fn fdiv_q() -> xmpz::fdiv_q_si, xmpz::fdiv_q }
    forward! { fn ediv_q() -> xmpz::ediv_q_si, xmpz::ediv_q }
    reverse! { fn tdiv_q_from() -> xmpz::si_tdiv_q, xmpz::tdiv_q }
    reverse! { fn cdiv_q_from() -> xmpz::si_cdiv_q, xmpz::cdiv_q }
    reverse! { fn fdiv_q_from() -> xmpz::si_fdiv_q, xmpz::fdiv_q }
    reverse! { fn ediv_q_from() -> xmpz::si_ediv_q, xmpz::ediv_q }
    forward! { fn tdiv_r() -> xmpz::tdiv_r_si, xmpz::tdiv_r }
    forward! { fn cdiv_r() -> xmpz::cdiv_r_si, xmpz::cdiv_r }
    forward! { fn fdiv_r() -> xmpz::fdiv_r_si, xmpz::fdiv_r }
    forward! { fn ediv_r() -> xmpz::ediv_r_si, xmpz::ediv_r }
    reverse! { fn tdiv_r_from() -> xmpz::si_tdiv_r, xmpz::tdiv_r }
    reverse! { fn cdiv_r_from() -> xmpz::si_cdiv_r, xmpz::cdiv_r }
    reverse! { fn fdiv_r_from() -> xmpz::si_fdiv_r, xmpz::fdiv_r }
    reverse! { fn ediv_r_from() -> xmpz::si_ediv_r, xmpz::ediv_r }
}

impl<T> PrimOps<c_ulong> for T
where
    T: AsLong<Long = c_ulong> + CheckedCast<c_ulong> + Into<SmallInteger>,
{
    forward! { fn tdiv_q() -> xmpz::tdiv_q_ui, xmpz::tdiv_q }
    forward! { fn cdiv_q() -> xmpz::cdiv_q_ui, xmpz::cdiv_q }
    forward! { fn fdiv_q() -> xmpz::fdiv_q_ui, xmpz::fdiv_q }
    forward! { fn ediv_q() -> xmpz::ediv_q_ui, xmpz::ediv_q }
    reverse! { fn tdiv_q_from() -> xmpz::ui_tdiv_q, xmpz::tdiv_q }
    reverse! { fn cdiv_q_from() -> xmpz::ui_cdiv_q, xmpz::cdiv_q }
    reverse! { fn fdiv_q_from() -> xmpz::ui_fdiv_q, xmpz::fdiv_q }
    reverse! { fn ediv_q_from() -> xmpz::ui_ediv_q, xmpz::ediv_q }
    forward! { fn tdiv_r() -> xmpz::tdiv_r_ui, xmpz::tdiv_r }
    forward! { fn cdiv_r() -> xmpz::cdiv_r_ui, xmpz::cdiv_r }
    forward! { fn fdiv_r() -> xmpz::fdiv_r_ui, xmpz::fdiv_r }
    forward! { fn ediv_r() -> xmpz::ediv_r_ui, xmpz::ediv_r }
    reverse! { fn tdiv_r_from() -> xmpz::ui_tdiv_r, xmpz::tdiv_r }
    reverse! { fn cdiv_r_from() -> xmpz::ui_cdiv_r, xmpz::cdiv_r }
    reverse! { fn fdiv_r_from() -> xmpz::ui_fdiv_r, xmpz::fdiv_r }
    reverse! { fn ediv_r_from() -> xmpz::ui_ediv_r, xmpz::ediv_r }
}

#[cfg(test)]
mod tests {
    use crate::ops::{DivRounding, RemRounding};
    use crate::Integer;
    use std::{i32, i64, u32, u64};

    #[test]
    fn check_div_prim_32() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u32::MAX];
        let s = [i32::MIN, -101, -100, -1, 0, 1, 100, 101, i32::MAX];
        let against = large
            .iter()
            .map(|&(n, s)| Integer::from(n) << s)
            .chain(s.iter().map(|&x| Integer::from(x)))
            .chain(u.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();
        for &op in &u {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().div_trunc(op), b.clone().div_trunc(&iop));
                    assert_eq!(b.clone().div_ceil(op), b.clone().div_ceil(&iop));
                    assert_eq!(b.clone().div_floor(op), b.clone().div_floor(&iop));
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        DivRounding::div_trunc(op, b.clone()),
                        iop.clone().div_trunc(b)
                    );
                    assert_eq!(
                        DivRounding::div_ceil(op, b.clone()),
                        iop.clone().div_ceil(b)
                    );
                    assert_eq!(
                        DivRounding::div_floor(op, b.clone()),
                        iop.clone().div_floor(b)
                    );
                    assert_eq!(DivRounding::div_euc(op, b.clone()), iop.clone().div_euc(b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().div_trunc(op), b.clone().div_trunc(&iop));
                    assert_eq!(b.clone().div_ceil(op), b.clone().div_ceil(&iop));
                    assert_eq!(b.clone().div_floor(op), b.clone().div_floor(&iop));
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        DivRounding::div_trunc(op, b.clone()),
                        iop.clone().div_trunc(b)
                    );
                    assert_eq!(
                        DivRounding::div_ceil(op, b.clone()),
                        iop.clone().div_ceil(b)
                    );
                    assert_eq!(
                        DivRounding::div_floor(op, b.clone()),
                        iop.clone().div_floor(b)
                    );
                    assert_eq!(DivRounding::div_euc(op, b.clone()), iop.clone().div_euc(b));
                }
            }
        }
    }

    #[test]
    fn check_rem_prim_32() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u32::MAX];
        let s = [i32::MIN, -101, -100, -1, 0, 1, 100, 101, i32::MAX];
        let against = large
            .iter()
            .map(|&(n, s)| Integer::from(n) << s)
            .chain(s.iter().map(|&x| Integer::from(x)))
            .chain(u.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();
        for &op in &u {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().rem_trunc(op), b.clone().rem_trunc(&iop));
                    assert_eq!(b.clone().rem_ceil(op), b.clone().rem_ceil(&iop));
                    assert_eq!(b.clone().rem_floor(op), b.clone().rem_floor(&iop));
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        RemRounding::rem_trunc(op, b.clone()),
                        iop.clone().rem_trunc(b)
                    );
                    assert_eq!(
                        RemRounding::rem_ceil(op, b.clone()),
                        iop.clone().rem_ceil(b)
                    );
                    assert_eq!(
                        RemRounding::rem_floor(op, b.clone()),
                        iop.clone().rem_floor(b)
                    );
                    assert_eq!(RemRounding::rem_euc(op, b.clone()), iop.clone().rem_euc(b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().rem_trunc(op), b.clone().rem_trunc(&iop));
                    assert_eq!(b.clone().rem_ceil(op), b.clone().rem_ceil(&iop));
                    assert_eq!(b.clone().rem_floor(op), b.clone().rem_floor(&iop));
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        RemRounding::rem_trunc(op, b.clone()),
                        iop.clone().rem_trunc(b)
                    );
                    assert_eq!(
                        RemRounding::rem_ceil(op, b.clone()),
                        iop.clone().rem_ceil(b)
                    );
                    assert_eq!(
                        RemRounding::rem_floor(op, b.clone()),
                        iop.clone().rem_floor(b)
                    );
                    assert_eq!(RemRounding::rem_euc(op, b.clone()), iop.clone().rem_euc(b));
                }
            }
        }
    }

    #[test]
    fn check_div_prim_64() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u64::MAX];
        let s = [i64::MIN, -101, -100, -1, 0, 1, 100, 101, i64::MAX];
        let against = large
            .iter()
            .map(|&(n, s)| Integer::from(n) << s)
            .chain(s.iter().map(|&x| Integer::from(x)))
            .chain(u.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();
        for &op in &u {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().div_trunc(op), b.clone().div_trunc(&iop));
                    assert_eq!(b.clone().div_ceil(op), b.clone().div_ceil(&iop));
                    assert_eq!(b.clone().div_floor(op), b.clone().div_floor(&iop));
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        DivRounding::div_trunc(op, b.clone()),
                        iop.clone().div_trunc(b)
                    );
                    assert_eq!(
                        DivRounding::div_ceil(op, b.clone()),
                        iop.clone().div_ceil(b)
                    );
                    assert_eq!(
                        DivRounding::div_floor(op, b.clone()),
                        iop.clone().div_floor(b)
                    );
                    assert_eq!(DivRounding::div_euc(op, b.clone()), iop.clone().div_euc(b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().div_trunc(op), b.clone().div_trunc(&iop));
                    assert_eq!(b.clone().div_ceil(op), b.clone().div_ceil(&iop));
                    assert_eq!(b.clone().div_floor(op), b.clone().div_floor(&iop));
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        DivRounding::div_trunc(op, b.clone()),
                        iop.clone().div_trunc(b)
                    );
                    assert_eq!(
                        DivRounding::div_ceil(op, b.clone()),
                        iop.clone().div_ceil(b)
                    );
                    assert_eq!(
                        DivRounding::div_floor(op, b.clone()),
                        iop.clone().div_floor(b)
                    );
                    assert_eq!(DivRounding::div_euc(op, b.clone()), iop.clone().div_euc(b));
                }
            }
        }
    }

    #[test]
    fn check_rem_prim_64() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u64::MAX];
        let s = [i64::MIN, -101, -100, -1, 0, 1, 100, 101, i64::MAX];
        let against = large
            .iter()
            .map(|&(n, s)| Integer::from(n) << s)
            .chain(s.iter().map(|&x| Integer::from(x)))
            .chain(u.iter().map(|&x| Integer::from(x)))
            .collect::<Vec<Integer>>();
        for &op in &u {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().rem_trunc(op), b.clone().rem_trunc(&iop));
                    assert_eq!(b.clone().rem_ceil(op), b.clone().rem_ceil(&iop));
                    assert_eq!(b.clone().rem_floor(op), b.clone().rem_floor(&iop));
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        RemRounding::rem_trunc(op, b.clone()),
                        iop.clone().rem_trunc(b)
                    );
                    assert_eq!(
                        RemRounding::rem_ceil(op, b.clone()),
                        iop.clone().rem_ceil(b)
                    );
                    assert_eq!(
                        RemRounding::rem_floor(op, b.clone()),
                        iop.clone().rem_floor(b)
                    );
                    assert_eq!(RemRounding::rem_euc(op, b.clone()), iop.clone().rem_euc(b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            for b in &against {
                if op != 0 {
                    assert_eq!(b.clone().rem_trunc(op), b.clone().rem_trunc(&iop));
                    assert_eq!(b.clone().rem_ceil(op), b.clone().rem_ceil(&iop));
                    assert_eq!(b.clone().rem_floor(op), b.clone().rem_floor(&iop));
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if *b != 0 {
                    assert_eq!(
                        RemRounding::rem_trunc(op, b.clone()),
                        iop.clone().rem_trunc(b)
                    );
                    assert_eq!(
                        RemRounding::rem_ceil(op, b.clone()),
                        iop.clone().rem_ceil(b)
                    );
                    assert_eq!(
                        RemRounding::rem_floor(op, b.clone()),
                        iop.clone().rem_floor(b)
                    );
                    assert_eq!(RemRounding::rem_euc(op, b.clone()), iop.clone().rem_euc(b));
                }
            }
        }
    }

    #[test]
    fn check_trunc() {
        let ndqr = [
            (23, 10, 2, 3),
            (23, -10, -2, 3),
            (-23, 10, -2, -3),
            (-23, -10, 2, -3),
            (20, 10, 2, 0),
            (20, -10, -2, 0),
            (-20, 10, -2, 0),
            (-20, -10, 2, 0),
            (3, 10, 0, 3),
            (3, -10, 0, 3),
            (-3, 10, 0, -3),
            (-3, -10, 0, -3),
            (0, 10, 0, 0),
            (0, -10, 0, 0),
        ];
        for &(n, d, q, r) in ndqr.iter() {
            assert_eq!(Integer::from(n) / d, q);
            assert_eq!(Integer::from(n).div_trunc(d), q);
            assert_eq!(Integer::from(n) % d, r);
            assert_eq!(Integer::from(n).rem_trunc(d), r);
            let qr = Integer::from(n).div_rem(Integer::from(d));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            let (mut nq, mut dr) = (Integer::from(n), Integer::from(d));
            let qr = <(Integer, Integer)>::from(nq.div_rem_ref(&dr));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            nq.div_rem_mut(&mut dr);
            assert_eq!(nq, q);
            assert_eq!(dr, r);
        }
    }

    #[test]
    fn check_ceil() {
        let ndqr = [
            (23, 10, 3, -7),
            (23, -10, -2, 3),
            (-23, 10, -2, -3),
            (-23, -10, 3, 7),
            (20, 10, 2, 0),
            (20, -10, -2, 0),
            (-20, 10, -2, 0),
            (-20, -10, 2, 0),
            (3, 10, 1, -7),
            (3, -10, 0, 3),
            (-3, 10, 0, -3),
            (-3, -10, 1, 7),
            (0, 10, 0, 0),
            (0, -10, 0, 0),
        ];
        for &(n, d, q, r) in ndqr.iter() {
            assert_eq!(Integer::from(n).div_ceil(d), q);
            assert_eq!(Integer::from(n).rem_ceil(d), r);
            let qr = Integer::from(n).div_rem_ceil(Integer::from(d));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            let (mut nq, mut dr) = (Integer::from(n), Integer::from(d));
            let qr = <(Integer, Integer)>::from(nq.div_rem_ceil_ref(&dr));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            nq.div_rem_ceil_mut(&mut dr);
            assert_eq!(nq, q);
            assert_eq!(dr, r);
        }
    }

    #[test]
    fn check_floor() {
        let ndqr = [
            (23, 10, 2, 3),
            (23, -10, -3, -7),
            (-23, 10, -3, 7),
            (-23, -10, 2, -3),
            (20, 10, 2, 0),
            (20, -10, -2, 0),
            (-20, 10, -2, 0),
            (-20, -10, 2, 0),
            (3, 10, 0, 3),
            (3, -10, -1, -7),
            (-3, 10, -1, 7),
            (-3, -10, 0, -3),
            (0, 10, 0, 0),
            (0, -10, 0, 0),
        ];
        for &(n, d, q, r) in ndqr.iter() {
            assert_eq!(Integer::from(n).div_floor(d), q);
            assert_eq!(Integer::from(n).rem_floor(d), r);
            let qr = Integer::from(n).div_rem_floor(Integer::from(d));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            let (mut nq, mut dr) = (Integer::from(n), Integer::from(d));
            let qr = <(Integer, Integer)>::from(nq.div_rem_floor_ref(&dr));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            nq.div_rem_floor_mut(&mut dr);
            assert_eq!(nq, q);
            assert_eq!(dr, r);
        }
    }

    #[test]
    fn check_euc() {
        let ndqr = [
            (23, 10, 2, 3),
            (23, -10, -2, 3),
            (-23, 10, -3, 7),
            (-23, -10, 3, 7),
            (20, 10, 2, 0),
            (20, -10, -2, 0),
            (-20, 10, -2, 0),
            (-20, -10, 2, 0),
            (3, 10, 0, 3),
            (3, -10, 0, 3),
            (-3, 10, -1, 7),
            (-3, -10, 1, 7),
            (0, 10, 0, 0),
            (0, -10, 0, 0),
        ];
        for &(n, d, q, r) in ndqr.iter() {
            assert_eq!(Integer::from(n).div_euc(d), q);
            assert_eq!(Integer::from(n).rem_euc(d), r);
            let qr = Integer::from(n).div_rem_euc(Integer::from(d));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            let (mut nq, mut dr) = (Integer::from(n), Integer::from(d));
            let qr = <(Integer, Integer)>::from(nq.div_rem_euc_ref(&dr));
            assert_eq!(qr.0, q);
            assert_eq!(qr.1, r);
            nq.div_rem_euc_mut(&mut dr);
            assert_eq!(nq, q);
            assert_eq!(dr, r);
        }
    }
}
