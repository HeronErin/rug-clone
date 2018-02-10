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

use {Assign, Integer};
use ext::gmp as xgmp;
use inner::{Inner, InnerMut};
use ops::{DivRounding, DivRoundingAssign, DivRoundingFrom, RemRounding,
          RemRoundingAssign, RemRoundingFrom};

// big / big -> Big
// big / &big -> Big
// &big / big -> Big
// &big / &big -> Ref
// big /= big
// big /= &big
// big /-> big
// &big /-> big
// struct Ref
// Ref -> Big
// big = Ref
macro_rules! div_op {
    {
        $trunc_fn:path, $ceil_fn:path, $floor_fn:path, $euc_fn:path;
        $Imp:ident $trunc:ident $ceil:ident $floor:ident $euc:ident;
        $ImpAssign:ident
            $trunc_assign:ident
            $ceil_assign:ident
            $floor_assign:ident
            $euc_assign:ident;
        $ImpFrom:ident
            $trunc_from:ident
            $ceil_from:ident
            $floor_from:ident
            $euc_from:ident;
        $Ref:ident
    } => {
        impl $Imp for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$trunc_assign(
                    &mut self,
                    &rhs,
                );
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$ceil_assign(
                    &mut self,
                    &rhs,
                );
                self
            }
            #[inline]
            fn $floor(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$floor_assign(
                    &mut self,
                    &rhs,
                );
                self
            }
            #[inline]
            fn $euc(mut self, rhs: Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$euc_assign(&mut self, &rhs);
                self
            }
        }

        impl<'i> $Imp<&'i Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: &'i Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$trunc_assign(
                    &mut self,
                    rhs,
                );
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: &'i Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$ceil_assign(&mut self, rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: &'i Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$floor_assign(
                    &mut self,
                    rhs,
                );
                self
            }
            #[inline]
            fn $euc(mut self, rhs: &'i Integer) -> Integer {
                <Integer as $ImpAssign<&Integer>>::$euc_assign(&mut self, rhs);
                self
            }
        }

        impl<'i> $Imp<Integer> for &'i Integer {
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
            type Output = $Ref<'i>;
            #[inline]
            fn $trunc(self, rhs: &'i Integer) -> $Ref {
                $Ref::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'i Integer) -> $Ref {
                $Ref::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'i Integer) -> $Ref {
                $Ref::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'i Integer) -> $Ref {
                $Ref::Euc(self, rhs)
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

        impl<'i> $ImpAssign<&'i Integer> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: &'i Integer) {
                unsafe {
                    $trunc_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: &'i Integer) {
                unsafe {
                    $ceil_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: &'i Integer) {
                unsafe {
                    $floor_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: &'i Integer) {
                unsafe {
                    $euc_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
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

        impl<'i> $ImpFrom<&'i Integer> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: &'i Integer) {
                unsafe {
                    $trunc_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: &'i Integer) {
                unsafe {
                    $ceil_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $floor_from(&mut self, lhs: &'i Integer) {
                unsafe {
                    $floor_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $euc_from(&mut self, lhs: &'i Integer) {
                unsafe {
                    $euc_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }

        #[derive(Clone, Copy)]
        pub enum $Ref<'i> {
            Trunc(&'i Integer, &'i Integer),
            Ceil(&'i Integer, &'i Integer),
            Floor(&'i Integer, &'i Integer),
            Euc(&'i Integer, &'i Integer),
        }

        impl<'i> Assign<$Ref<'i>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Ref<'i>) {
                match src {
                    $Ref::Trunc(lhs, rhs) => unsafe {
                        $trunc_fn(self.inner_mut(), lhs.inner(), rhs.inner());
                    },
                    $Ref::Ceil(lhs, rhs) => unsafe {
                        $ceil_fn(self.inner_mut(), lhs.inner(), rhs.inner());
                    },
                    $Ref::Floor(lhs, rhs) => unsafe {
                        $floor_fn(self.inner_mut(), lhs.inner(), rhs.inner());
                    },
                    $Ref::Euc(lhs, rhs) => unsafe {
                        $euc_fn(self.inner_mut(), lhs.inner(), rhs.inner());
                    },
                }
            }
        }

        impl<'i> From<$Ref<'i>> for Integer {
            #[inline]
            fn from(src: $Ref<'i>) -> Self {
                let mut dst = Integer::new();
                dst.assign(src);
                dst
            }
        }
    }
}

// big / prim -> Big
// big / &prim -> Big
// &big / prim -> Ref
// &big / &prim -> Ref
// big /= prim
// big /= &prim
// struct Ref
// Ref -> Big
// big = Ref
// prim / big -> Big
// prim / &big -> FromRef
// &prim / big -> Big
// &prim / &big -> FromRef
// prim /-> big
// &prim /-> big
// struct FromRef
// FromRef -> Big
// big = FromRef
macro_rules! div_prim {
    {
        $trunc_fn:path, $ceil_fn:path, $floor_fn:path, $euc_fn:path;
        $trunc_from_fn:path,
        $ceil_from_fn:path,
        $floor_from_fn:path,
        $euc_from_fn:path;
        $Imp:ident $trunc:ident $ceil:ident $floor:ident $euc:ident;
        $ImpAssign:ident
            $trunc_assign:ident
            $ceil_assign:ident
            $floor_assign:ident
            $euc_assign:ident;
        $ImpFrom:ident
            $trunc_from:ident
            $ceil_from:ident
            $floor_from:ident
            $euc_from:ident;
        $T:ty;
        $Ref:ident $FromRef:ident
    } => {
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

        impl<'t> $Imp<&'t $T> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: &'t $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$trunc_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: &'t $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$ceil_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: &'t $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$floor_assign(&mut self, *rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: &'t $T) -> Integer {
                <Integer as $ImpAssign<$T>>::$euc_assign(&mut self, *rhs);
                self
            }
        }

        impl<'i> $Imp<$T> for &'i Integer {
            type Output = $Ref<'i>;
            #[inline]
            fn $trunc(self, rhs: $T) -> $Ref<'i> {
                $Ref::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: $T) -> $Ref<'i> {
                $Ref::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: $T) -> $Ref<'i> {
                $Ref::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: $T) -> $Ref<'i> {
                $Ref::Euc(self, rhs)
            }
        }

        impl<'t, 'i> $Imp<&'t $T> for &'i Integer {
            type Output = $Ref<'i>;
            #[inline]
            fn $trunc(self, rhs: &'t $T) -> $Ref<'i> {
                <&Integer as $Imp<$T>>::$trunc(self, *rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'t $T) -> $Ref<'i> {
                <&Integer as $Imp<$T>>::$ceil(self, *rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'t $T) -> $Ref<'i> {
                <&Integer as $Imp<$T>>::$floor(self, *rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'t $T) -> $Ref<'i> {
                <&Integer as $Imp<$T>>::$euc(self, *rhs)
            }
        }

        impl $ImpAssign<$T> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: $T) {
                unsafe {
                    $trunc_fn(self.inner_mut(), self.inner(), rhs.into());
                }
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: $T) {
                unsafe {
                    $ceil_fn(self.inner_mut(), self.inner(), rhs.into());
                }
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: $T) {
                unsafe {
                    $floor_fn(self.inner_mut(), self.inner(), rhs.into());
                }
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: $T) {
                unsafe {
                    $euc_fn(self.inner_mut(), self.inner(), rhs.into());
                }
            }
        }

        impl<'t> $ImpAssign<&'t $T> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: &'t $T) {
                <Integer as $ImpAssign<$T>>::$trunc_assign(self, *rhs);
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: &'t $T) {
                <Integer as $ImpAssign<$T>>::$ceil_assign(self, *rhs);
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: &'t $T) {
                <Integer as $ImpAssign<$T>>::$floor_assign(self, *rhs);
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: &'t $T) {
                <Integer as $ImpAssign<$T>>::$euc_assign(self, *rhs);
            }
        }

        #[derive(Clone, Copy)]
        pub enum $Ref<'i> {
            Trunc(&'i Integer, $T),
            Ceil(&'i Integer, $T),
            Floor(&'i Integer, $T),
            Euc(&'i Integer, $T),
        }

        impl<'i> Assign<$Ref<'i>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Ref<'i>) {
                match src {
                    $Ref::Trunc(lhs, rhs) => unsafe {
                        $trunc_fn(self.inner_mut(), lhs.inner(), rhs.into());
                    },
                    $Ref::Ceil(lhs, rhs) => unsafe {
                        $ceil_fn(self.inner_mut(), lhs.inner(), rhs.into());
                    },
                    $Ref::Floor(lhs, rhs) => unsafe {
                        $floor_fn(self.inner_mut(), lhs.inner(), rhs.into());
                    },
                    $Ref::Euc(lhs, rhs) => unsafe {
                        $euc_fn(self.inner_mut(), lhs.inner(), rhs.into());
                    },
                }
            }
        }

        impl<'i> From<$Ref<'i>> for Integer {
            #[inline]
            fn from(src: $Ref<'i>) -> Self {
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
            type Output = $FromRef<'i>;
            #[inline]
            fn $trunc(self, rhs: &'i Integer) -> $FromRef<'i> {
                $FromRef::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'i Integer) -> $FromRef<'i> {
                $FromRef::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'i Integer) -> $FromRef<'i> {
                $FromRef::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'i Integer) -> $FromRef<'i> {
                $FromRef::Euc(self, rhs)
            }
        }

        impl<'t> $Imp<Integer> for &'t $T {
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

        impl<'i, 't> $Imp<&'i Integer> for &'t $T {
            type Output = $FromRef<'i>;
            #[inline]
            fn $trunc(self, rhs: &'i Integer) -> $FromRef<'i> {
                <$T as $Imp<&Integer>>::$trunc(*self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'i Integer) -> $FromRef<'i> {
                <$T as $Imp<&Integer>>::$ceil(*self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'i Integer) -> $FromRef<'i> {
                <$T as $Imp<&Integer>>::$floor(*self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'i Integer) -> $FromRef<'i> {
                <$T as $Imp<&Integer>>::$euc(*self, rhs)
            }
        }

        impl $ImpFrom<$T> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: $T) {
                unsafe {
                    $trunc_from_fn(self.inner_mut(), lhs.into(), self.inner());
                }
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: $T) {
                unsafe {
                    $ceil_from_fn(self.inner_mut(), lhs.into(), self.inner());
                }
            }
            #[inline]
            fn $floor_from(&mut self, lhs: $T) {
                unsafe {
                    $floor_from_fn(self.inner_mut(), lhs.into(), self.inner());
                }
            }
            #[inline]
            fn $euc_from(&mut self, lhs: $T) {
                unsafe {
                    $euc_from_fn(self.inner_mut(), lhs.into(), self.inner());
                }
            }
        }

        impl<'t> $ImpFrom<&'t $T> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: &'t $T) {
                <Integer as $ImpFrom<$T>>::$trunc_from(self, *lhs);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: &'t $T) {
                <Integer as $ImpFrom<$T>>::$ceil_from(self, *lhs);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: &'t $T) {
                <Integer as $ImpFrom<$T>>::$floor_from(self, *lhs);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: &'t $T) {
                <Integer as $ImpFrom<$T>>::$euc_from(self, *lhs);
            }
        }

        #[derive(Clone, Copy)]
        pub enum $FromRef<'i> {
            Trunc($T, &'i Integer),
            Ceil($T, &'i Integer),
            Floor($T, &'i Integer),
            Euc($T, &'i Integer),
        }

        impl<'i> Assign<$FromRef<'i>> for Integer {
            #[inline]
            fn assign(&mut self, src: $FromRef<'i>) {
                match src {
                    $FromRef::Trunc(lhs, rhs) => unsafe {
                        $trunc_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $FromRef::Ceil(lhs, rhs) => unsafe {
                        $ceil_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $FromRef::Floor(lhs, rhs) => unsafe {
                        $floor_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $FromRef::Euc(lhs, rhs) => unsafe {
                        $euc_from_fn(self.inner_mut(), lhs.into(), rhs.inner());
                    },
                }
            }
        }

        impl<'i> From<$FromRef<'i>> for Integer {
            #[inline]
            fn from(src: $FromRef<'i>) -> Self {
                let mut dst = Integer::new();
                dst.assign(src);
                dst
            }
        }
    }
}

div_op! {
    xgmp::mpz_tdiv_q_check,
    xgmp::mpz_cdiv_q_check,
    xgmp::mpz_fdiv_q_check,
    xgmp::mpz_ediv_q_check;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    DivRoundingRef
}
div_op! {
    xgmp::mpz_tdiv_r_check,
    xgmp::mpz_cdiv_r_check,
    xgmp::mpz_fdiv_r_check,
    xgmp::mpz_ediv_r_check;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    RemRoundingRef
}

div_prim! {
    xgmp::mpz_tdiv_q_si_check,
    xgmp::mpz_cdiv_q_si_check,
    xgmp::mpz_fdiv_q_si_check,
    xgmp::mpz_ediv_q_si_check;
    xgmp::mpz_si_tdiv_q_check,
    xgmp::mpz_si_cdiv_q_check,
    xgmp::mpz_si_fdiv_q_check,
    xgmp::mpz_si_ediv_q_check;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    i32;
    DivRoundingI32Ref DivRoundingFromI32Ref
}
div_prim! {
    xgmp::mpz_tdiv_r_si_check,
    xgmp::mpz_cdiv_r_si_check,
    xgmp::mpz_fdiv_r_si_check,
    xgmp::mpz_ediv_r_si_check;
    xgmp::mpz_si_tdiv_r_check,
    xgmp::mpz_si_cdiv_r_check,
    xgmp::mpz_si_fdiv_r_check,
    xgmp::mpz_si_ediv_r_check;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    i32;
    RemRoundingI32Ref RemRoundingFromI32Ref
}
div_prim! {
    xgmp::mpz_tdiv_q_ui_check,
    xgmp::mpz_cdiv_q_ui_check,
    xgmp::mpz_fdiv_q_ui_check,
    xgmp::mpz_ediv_q_ui_check;
    xgmp::mpz_ui_tdiv_q_check,
    xgmp::mpz_ui_cdiv_q_check,
    xgmp::mpz_ui_fdiv_q_check,
    xgmp::mpz_ui_ediv_q_check;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    u32;
    DivRoundingU32Ref DivRoundingFromU32Ref
}
div_prim! {
    xgmp::mpz_tdiv_r_ui_check,
    xgmp::mpz_cdiv_r_ui_check,
    xgmp::mpz_fdiv_r_ui_check,
    xgmp::mpz_ediv_r_ui_check;
    xgmp::mpz_ui_tdiv_r_check,
    xgmp::mpz_ui_cdiv_r_check,
    xgmp::mpz_ui_fdiv_r_check,
    xgmp::mpz_ui_ediv_r_check;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    u32;
    RemRoundingU32Ref RemRoundingFromU32Ref
}

#[cfg(test)]
mod tests {
    use Integer;
    use ops::{DivRounding, RemRounding};
    use std::{i32, u32};

    #[test]
    fn check_div_prim() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u32::MAX];
        let s = [i32::MIN, -101, -100, -1, 0, 1, 100, 101, i32::MAX];
        for &op in &u {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                if op != 0 {
                    assert_eq!(
                        b.clone().div_trunc(op),
                        b.clone().div_trunc(&iop)
                    );
                    assert_eq!(
                        b.clone().div_ceil(op),
                        b.clone().div_ceil(&iop)
                    );
                    assert_eq!(
                        b.clone().div_floor(op),
                        b.clone().div_floor(&iop)
                    );
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if b != 0 {
                    assert_eq!(
                        op.div_trunc(b.clone()),
                        iop.clone().div_trunc(&b)
                    );
                    assert_eq!(
                        op.div_ceil(b.clone()),
                        iop.clone().div_ceil(&b)
                    );
                    assert_eq!(
                        op.div_floor(b.clone()),
                        iop.clone().div_floor(&b)
                    );
                    assert_eq!(op.div_euc(b.clone()), iop.clone().div_euc(&b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                if op != 0 {
                    assert_eq!(
                        b.clone().div_trunc(op),
                        b.clone().div_trunc(&iop)
                    );
                    assert_eq!(
                        b.clone().div_ceil(op),
                        b.clone().div_ceil(&iop)
                    );
                    assert_eq!(
                        b.clone().div_floor(op),
                        b.clone().div_floor(&iop)
                    );
                    assert_eq!(b.clone().div_euc(op), b.clone().div_euc(&iop));
                }
                if b != 0 {
                    assert_eq!(
                        op.div_trunc(b.clone()),
                        iop.clone().div_trunc(&b)
                    );
                    assert_eq!(
                        op.div_ceil(b.clone()),
                        iop.clone().div_ceil(&b)
                    );
                    assert_eq!(
                        op.div_floor(b.clone()),
                        iop.clone().div_floor(&b)
                    );
                    assert_eq!(op.div_euc(b.clone()), iop.clone().div_euc(&b));
                }
            }
        }
    }

    #[test]
    fn check_rem_prim() {
        let large = [(1, 100), (-11, 200), (33, 150)];
        let u = [0, 1, 100, 101, u32::MAX];
        let s = [i32::MIN, -101, -100, -1, 0, 1, 100, 101, i32::MAX];
        for &op in &u {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                if op != 0 {
                    assert_eq!(
                        b.clone().rem_trunc(op),
                        b.clone().rem_trunc(&iop)
                    );
                    assert_eq!(
                        b.clone().rem_ceil(op),
                        b.clone().rem_ceil(&iop)
                    );
                    assert_eq!(
                        b.clone().rem_floor(op),
                        b.clone().rem_floor(&iop)
                    );
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if b != 0 {
                    assert_eq!(
                        op.rem_trunc(b.clone()),
                        iop.clone().rem_trunc(&b)
                    );
                    assert_eq!(
                        op.rem_ceil(b.clone()),
                        iop.clone().rem_ceil(&b)
                    );
                    assert_eq!(
                        op.rem_floor(b.clone()),
                        iop.clone().rem_floor(&b)
                    );
                    assert_eq!(op.rem_euc(b.clone()), iop.clone().rem_euc(&b));
                }
            }
        }
        for &op in &s {
            let iop = Integer::from(op);
            let against = (large.iter().map(|&(n, s)| Integer::from(n) << s))
                .chain(s.iter().map(|&x| Integer::from(x)))
                .chain(u.iter().map(|&x| Integer::from(x)));
            for b in against {
                if op != 0 {
                    assert_eq!(
                        b.clone().rem_trunc(op),
                        b.clone().rem_trunc(&iop)
                    );
                    assert_eq!(
                        b.clone().rem_ceil(op),
                        b.clone().rem_ceil(&iop)
                    );
                    assert_eq!(
                        b.clone().rem_floor(op),
                        b.clone().rem_floor(&iop)
                    );
                    assert_eq!(b.clone().rem_euc(op), b.clone().rem_euc(&iop));
                }
                if b != 0 {
                    assert_eq!(
                        op.rem_trunc(b.clone()),
                        iop.clone().rem_trunc(&b)
                    );
                    assert_eq!(
                        op.rem_ceil(b.clone()),
                        iop.clone().rem_ceil(&b)
                    );
                    assert_eq!(
                        op.rem_floor(b.clone()),
                        iop.clone().rem_floor(&b)
                    );
                    assert_eq!(op.rem_euc(b.clone()), iop.clone().rem_euc(&b));
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
