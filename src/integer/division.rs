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

use {Assign, Integer};
use ext::gmp as xgmp;
use inner::{Inner, InnerMut};
use ops::{DivRounding, DivRoundingAssign, DivRoundingFrom, RemRounding,
          RemRoundingAssign, RemRoundingFrom};

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
        impl $Imp<Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(self, rhs: Integer) -> Integer {
                self.$trunc(&rhs)
            }
            #[inline]
            fn $ceil(self, rhs: Integer) -> Integer {
                self.$ceil(&rhs)
            }
            #[inline]
            fn $floor(self, rhs: Integer) -> Integer {
                self.$floor(&rhs)
            }
            #[inline]
            fn $euc(self, rhs: Integer) -> Integer {
                self.$euc(&rhs)
            }
        }

        impl<'a> $Imp<&'a Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: &'a Integer) -> Integer {
                self.$trunc_assign(rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: &'a Integer) -> Integer {
                self.$ceil_assign(rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: &'a Integer) -> Integer {
                self.$floor_assign(rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: &'a Integer) -> Integer {
                self.$euc_assign(rhs);
                self
            }
        }

        impl<'a> $Imp<Integer> for &'a Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(self, mut rhs: Integer) -> Integer {
                rhs.$trunc_from(self);
                rhs
            }
            #[inline]
            fn $ceil(self, mut rhs: Integer) -> Integer {
                rhs.$ceil_from(self);
                rhs
            }
            #[inline]
            fn $floor(self, mut rhs: Integer) -> Integer {
                rhs.$floor_from(self);
                rhs
            }
            #[inline]
            fn $euc(self, mut rhs: Integer) -> Integer {
                rhs.$euc_from(self);
                rhs
            }
        }

        impl $ImpAssign<Integer> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: Integer) {
                self.$trunc_assign(&rhs);
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: Integer) {
                self.$ceil_assign(&rhs);
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: Integer) {
                self.$floor_assign(&rhs);
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: Integer) {
                self.$euc_assign(&rhs);
            }
        }

        impl<'a> $ImpAssign<&'a Integer> for Integer {
            #[inline]
            fn $trunc_assign(&mut self, rhs: &'a Integer) {
                unsafe {
                    $trunc_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $ceil_assign(&mut self, rhs: &'a Integer) {
                unsafe {
                    $ceil_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $floor_assign(&mut self, rhs: &'a Integer) {
                unsafe {
                    $floor_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
            #[inline]
            fn $euc_assign(&mut self, rhs: &'a Integer) {
                unsafe {
                    $euc_fn(self.inner_mut(), self.inner(), rhs.inner());
                }
            }
        }

        impl $ImpFrom<Integer> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: Integer) {
                self.$trunc_from(&lhs);
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: Integer) {
                self.$ceil_from(&lhs);
            }
            #[inline]
            fn $floor_from(&mut self, lhs: Integer) {
                self.$floor_from(&lhs);
            }
            #[inline]
            fn $euc_from(&mut self, lhs: Integer) {
                self.$euc_from(&lhs);
            }
        }

        impl<'a> $ImpFrom<&'a Integer> for Integer {
            #[inline]
            fn $trunc_from(&mut self, lhs: &'a Integer) {
                unsafe {
                    $trunc_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $ceil_from(&mut self, lhs: &'a Integer) {
                unsafe {
                    $ceil_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $floor_from(&mut self, lhs: &'a Integer) {
                unsafe {
                    $floor_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
            #[inline]
            fn $euc_from(&mut self, lhs: &'a Integer) {
                unsafe {
                    $euc_fn(self.inner_mut(), lhs.inner(), self.inner());
                }
            }
        }

        impl<'a> $Imp<&'a Integer> for &'a Integer {
            type Output = $Ref<'a>;
            #[inline]
            fn $trunc(self, rhs: &'a Integer) -> $Ref {
                $Ref::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'a Integer) -> $Ref {
                $Ref::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'a Integer) -> $Ref {
                $Ref::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'a Integer) -> $Ref {
                $Ref::Euc(self, rhs)
            }
        }

        #[derive(Clone, Copy)]
        pub enum $Ref<'a> {
            Trunc(&'a Integer, &'a Integer),
            Ceil(&'a Integer, &'a Integer),
            Floor(&'a Integer, &'a Integer),
            Euc(&'a Integer, &'a Integer),
        }

        from_borrow! { $Ref<'a> => Integer }

        impl<'a> Assign<$Ref<'a>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Ref) {
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
    }
}

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
        $Ref:ident $RefFrom:ident
    } => {
        impl $Imp<$T> for Integer {
            type Output = Integer;
            #[inline]
            fn $trunc(mut self, rhs: $T) -> Integer {
                self.$trunc_assign(rhs);
                self
            }
            #[inline]
            fn $ceil(mut self, rhs: $T) -> Integer {
                self.$ceil_assign(rhs);
                self
            }
            #[inline]
            fn $floor(mut self, rhs: $T) -> Integer {
                self.$floor_assign(rhs);
                self
            }
            #[inline]
            fn $euc(mut self, rhs: $T) -> Integer {
                self.$euc_assign(rhs);
                self
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

        impl<'a> $Imp<$T> for &'a Integer {
            type Output = $Ref<'a>;
            #[inline]
            fn $trunc(self, rhs: $T) -> $Ref<'a> {
                $Ref::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: $T) -> $Ref<'a> {
                $Ref::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: $T) -> $Ref<'a> {
                $Ref::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: $T) -> $Ref<'a> {
                $Ref::Euc(self, rhs)
            }
        }

        #[derive(Clone, Copy)]
        pub enum $Ref<'a> {
            Trunc(&'a Integer, $T),
            Ceil(&'a Integer, $T),
            Floor(&'a Integer, $T),
            Euc(&'a Integer, $T),
        }

        from_borrow! { $Ref<'a> => Integer }

        impl<'a> Assign<$Ref<'a>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Ref) {
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

        impl $Imp<Integer> for $T {
            type Output = Integer;
            #[inline]
            fn $trunc(self, mut rhs: Integer) -> Integer {
                rhs.$trunc_from(self);
                rhs
            }
            #[inline]
            fn $ceil(self, mut rhs: Integer) -> Integer {
                rhs.$ceil_from(self);
                rhs
            }
            #[inline]
            fn $floor(self, mut rhs: Integer) -> Integer {
                rhs.$floor_from(self);
                rhs
            }
            #[inline]
            fn $euc(self, mut rhs: Integer) -> Integer {
                rhs.$euc_from(self);
                rhs
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

        impl<'a> $Imp<&'a Integer> for $T {
            type Output = $RefFrom<'a>;
            #[inline]
            fn $trunc(self, rhs: &'a Integer) -> $RefFrom<'a> {
                $RefFrom::Trunc(self, rhs)
            }
            #[inline]
            fn $ceil(self, rhs: &'a Integer) -> $RefFrom<'a> {
                $RefFrom::Ceil(self, rhs)
            }
            #[inline]
            fn $floor(self, rhs: &'a Integer) -> $RefFrom<'a> {
                $RefFrom::Floor(self, rhs)
            }
            #[inline]
            fn $euc(self, rhs: &'a Integer) -> $RefFrom<'a> {
                $RefFrom::Euc(self, rhs)
            }
        }

        #[derive(Clone, Copy)]
        pub enum $RefFrom<'a> {
            Trunc($T, &'a Integer),
            Ceil($T, &'a Integer),
            Floor($T, &'a Integer),
            Euc($T, &'a Integer),
        }

        from_borrow! { $RefFrom<'a> => Integer }

        impl<'a> Assign<$RefFrom<'a>> for Integer {
            #[inline]
            fn assign(&mut self, src: $RefFrom) {
                match src {
                    $RefFrom::Trunc(lhs, rhs) => unsafe {
                        $trunc_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $RefFrom::Ceil(lhs, rhs) => unsafe {
                        $ceil_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $RefFrom::Floor(lhs, rhs) => unsafe {
                        $floor_from_fn(
                            self.inner_mut(),
                            lhs.into(),
                            rhs.inner(),
                        );
                    },
                    $RefFrom::Euc(lhs, rhs) => unsafe {
                        $euc_from_fn(self.inner_mut(), lhs.into(), rhs.inner());
                    },
                }
            }
        }
    }
}

div_op! {
    xgmp::mpz_tdiv_q_check_0,
    xgmp::mpz_cdiv_q_check_0,
    xgmp::mpz_fdiv_q_check_0,
    xgmp::mpz_ediv_q_check_0;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    DivRoundingRef
}
div_op! {
    xgmp::mpz_tdiv_r_check_0,
    xgmp::mpz_cdiv_r_check_0,
    xgmp::mpz_fdiv_r_check_0,
    xgmp::mpz_ediv_r_check_0;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    RemRoundingRef
}

div_prim! {
    xgmp::mpz_tdiv_q_si_check_0,
    xgmp::mpz_cdiv_q_si_check_0,
    xgmp::mpz_fdiv_q_si_check_0,
    xgmp::mpz_ediv_q_si_check_0;
    xgmp::mpz_si_tdiv_q_check_0,
    xgmp::mpz_si_cdiv_q_check_0,
    xgmp::mpz_si_fdiv_q_check_0,
    xgmp::mpz_si_ediv_q_check_0;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    i32;
    DivRoundingRefI32 DivRoundingFromRefI32
}
div_prim! {
    xgmp::mpz_tdiv_r_si_check_0,
    xgmp::mpz_cdiv_r_si_check_0,
    xgmp::mpz_fdiv_r_si_check_0,
    xgmp::mpz_ediv_r_si_check_0;
    xgmp::mpz_si_tdiv_r_check_0,
    xgmp::mpz_si_cdiv_r_check_0,
    xgmp::mpz_si_fdiv_r_check_0,
    xgmp::mpz_si_ediv_r_check_0;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    i32;
    RemRoundingRefI32 RemRoundingFromRefI32
}
div_prim! {
    xgmp::mpz_tdiv_q_ui_check_0,
    xgmp::mpz_cdiv_q_ui_check_0,
    xgmp::mpz_fdiv_q_ui_check_0,
    xgmp::mpz_ediv_q_ui_check_0;
    xgmp::mpz_ui_tdiv_q_check_0,
    xgmp::mpz_ui_cdiv_q_check_0,
    xgmp::mpz_ui_fdiv_q_check_0,
    xgmp::mpz_ui_ediv_q_check_0;
    DivRounding div_trunc div_ceil div_floor div_euc;
    DivRoundingAssign
        div_trunc_assign div_ceil_assign div_floor_assign div_euc_assign;
    DivRoundingFrom
        div_trunc_from div_ceil_from div_floor_from div_euc_from;
    u32;
    DivRoundingRefU32 DivRoundingFromRefU32
}
div_prim! {
    xgmp::mpz_tdiv_r_ui_check_0,
    xgmp::mpz_cdiv_r_ui_check_0,
    xgmp::mpz_fdiv_r_ui_check_0,
    xgmp::mpz_ediv_r_ui_check_0;
    xgmp::mpz_ui_tdiv_r_check_0,
    xgmp::mpz_ui_cdiv_r_check_0,
    xgmp::mpz_ui_fdiv_r_check_0,
    xgmp::mpz_ui_ediv_r_check_0;
    RemRounding rem_trunc rem_ceil rem_floor rem_euc;
    RemRoundingAssign
        rem_trunc_assign rem_ceil_assign rem_floor_assign rem_euc_assign;
    RemRoundingFrom
        rem_trunc_from rem_ceil_from rem_floor_from rem_euc_from;
    u32;
    RemRoundingRefU32 RemRoundingFromRefU32
}
