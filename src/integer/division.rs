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
use ops::{DivFrom, DivRemRounding, DivRemRoundingAssign, DivRemRoundingFrom,
          RemFrom};
use std::cmp::Ordering;
use std::ops::{DivAssign, RemAssign};

impl DivRemRounding<Integer> for Integer {
    type DivOutput = Integer;
    type RemOutput = Integer;
    #[inline]
    fn div_trunc(self, rhs: Integer) -> Integer {
        self.div_trunc(&rhs)
    }
    #[inline]
    fn rem_trunc(self, rhs: Integer) -> Integer {
        self.rem_trunc(&rhs)
    }
    #[inline]
    fn div_ceil(self, rhs: Integer) -> Integer {
        self.div_ceil(&rhs)
    }
    #[inline]
    fn rem_ceil(self, rhs: Integer) -> Integer {
        self.rem_ceil(&rhs)
    }
    #[inline]
    fn div_floor(self, rhs: Integer) -> Integer {
        self.div_floor(&rhs)
    }
    #[inline]
    fn rem_floor(self, rhs: Integer) -> Integer {
        self.rem_floor(&rhs)
    }
    #[inline]
    fn div_euc(self, rhs: Integer) -> Integer {
        self.div_euc(&rhs)
    }
    #[inline]
    fn rem_euc(self, rhs: Integer) -> Integer {
        self.rem_euc(&rhs)
    }
}

impl<'a> DivRemRounding<&'a Integer> for Integer {
    type DivOutput = Integer;
    type RemOutput = Integer;
    #[inline]
    fn div_trunc(mut self, rhs: &'a Integer) -> Integer {
        self.div_trunc_assign(rhs);
        self
    }
    #[inline]
    fn rem_trunc(mut self, rhs: &'a Integer) -> Integer {
        self.rem_trunc_assign(rhs);
        self
    }
    #[inline]
    fn div_ceil(mut self, rhs: &'a Integer) -> Integer {
        self.div_ceil_assign(rhs);
        self
    }
    #[inline]
    fn rem_ceil(mut self, rhs: &'a Integer) -> Integer {
        self.rem_ceil_assign(rhs);
        self
    }
    #[inline]
    fn div_floor(mut self, rhs: &'a Integer) -> Integer {
        self.div_floor_assign(rhs);
        self
    }
    #[inline]
    fn rem_floor(mut self, rhs: &'a Integer) -> Integer {
        self.rem_floor_assign(rhs);
        self
    }
    #[inline]
    fn div_euc(mut self, rhs: &'a Integer) -> Integer {
        self.div_euc_assign(rhs);
        self
    }
    #[inline]
    fn rem_euc(mut self, rhs: &'a Integer) -> Integer {
        self.rem_euc_assign(rhs);
        self
    }
}

impl<'a> DivRemRounding<Integer> for &'a Integer {
    type DivOutput = Integer;
    type RemOutput = Integer;
    #[inline]
    fn div_trunc(self, mut rhs: Integer) -> Integer {
        rhs.div_trunc_from(self);
        rhs
    }
    #[inline]
    fn rem_trunc(self, mut rhs: Integer) -> Integer {
        rhs.rem_trunc_from(self);
        rhs
    }
    #[inline]
    fn div_ceil(self, mut rhs: Integer) -> Integer {
        rhs.div_ceil_from(self);
        rhs
    }
    #[inline]
    fn rem_ceil(self, mut rhs: Integer) -> Integer {
        rhs.rem_ceil_from(self);
        rhs
    }
    #[inline]
    fn div_floor(self, mut rhs: Integer) -> Integer {
        rhs.div_floor_from(self);
        rhs
    }
    #[inline]
    fn rem_floor(self, mut rhs: Integer) -> Integer {
        rhs.rem_floor_from(self);
        rhs
    }
    #[inline]
    fn div_euc(self, mut rhs: Integer) -> Integer {
        rhs.div_euc_from(self);
        rhs
    }
    #[inline]
    fn rem_euc(self, mut rhs: Integer) -> Integer {
        rhs.rem_euc_from(self);
        rhs
    }
}

impl DivRemRoundingAssign<Integer> for Integer {
    #[inline]
    fn div_trunc_assign(&mut self, rhs: Integer) {
        self.div_trunc_assign(&rhs);
    }
    #[inline]
    fn rem_trunc_assign(&mut self, rhs: Integer) {
        self.rem_trunc_assign(&rhs);
    }
    #[inline]
    fn div_ceil_assign(&mut self, rhs: Integer) {
        self.div_ceil_assign(&rhs);
    }
    #[inline]
    fn rem_ceil_assign(&mut self, rhs: Integer) {
        self.rem_ceil_assign(&rhs);
    }
    #[inline]
    fn div_floor_assign(&mut self, rhs: Integer) {
        self.div_floor_assign(&rhs);
    }
    #[inline]
    fn rem_floor_assign(&mut self, rhs: Integer) {
        self.rem_floor_assign(&rhs);
    }
    #[inline]
    fn div_euc_assign(&mut self, rhs: Integer) {
        self.div_euc_assign(&rhs);
    }
    #[inline]
    fn rem_euc_assign(&mut self, rhs: Integer) {
        self.rem_euc_assign(&rhs);
    }
}

impl<'a> DivRemRoundingAssign<&'a Integer> for Integer {
    #[inline]
    fn div_trunc_assign(&mut self, rhs: &'a Integer) {
        self.div_assign(rhs);
    }
    #[inline]
    fn rem_trunc_assign(&mut self, rhs: &'a Integer) {
        self.rem_assign(rhs);
    }
    #[inline]
    fn div_ceil_assign(&mut self, rhs: &'a Integer) {
        unsafe {
            xgmp::mpz_cdiv_q_check_0(
                self.inner_mut(),
                self.inner(),
                rhs.inner(),
            );
        }
    }
    #[inline]
    fn rem_ceil_assign(&mut self, rhs: &'a Integer) {
        unsafe {
            xgmp::mpz_cdiv_r_check_0(
                self.inner_mut(),
                self.inner(),
                rhs.inner(),
            );
        }
    }
    #[inline]
    fn div_floor_assign(&mut self, rhs: &'a Integer) {
        unsafe {
            xgmp::mpz_fdiv_q_check_0(
                self.inner_mut(),
                self.inner(),
                rhs.inner(),
            );
        }
    }
    #[inline]
    fn rem_floor_assign(&mut self, rhs: &'a Integer) {
        unsafe {
            xgmp::mpz_fdiv_r_check_0(
                self.inner_mut(),
                self.inner(),
                rhs.inner(),
            );
        }
    }
    #[inline]
    fn div_euc_assign(&mut self, rhs: &'a Integer) {
        if rhs.cmp0() == Ordering::Greater {
            self.div_floor_assign(rhs);
        } else {
            self.div_ceil_assign(rhs);
        }
    }
    #[inline]
    fn rem_euc_assign(&mut self, rhs: &'a Integer) {
        if rhs.cmp0() == Ordering::Greater {
            self.rem_floor_assign(rhs);
        } else {
            self.rem_ceil_assign(rhs);
        }
    }
}

impl DivRemRoundingFrom<Integer> for Integer {
    #[inline]
    fn div_trunc_from(&mut self, lhs: Integer) {
        self.div_trunc_from(&lhs);
    }
    #[inline]
    fn rem_trunc_from(&mut self, lhs: Integer) {
        self.rem_trunc_from(&lhs);
    }
    #[inline]
    fn div_ceil_from(&mut self, lhs: Integer) {
        self.div_ceil_from(&lhs);
    }
    #[inline]
    fn rem_ceil_from(&mut self, lhs: Integer) {
        self.rem_ceil_from(&lhs);
    }
    #[inline]
    fn div_floor_from(&mut self, lhs: Integer) {
        self.div_floor_from(&lhs);
    }
    #[inline]
    fn rem_floor_from(&mut self, lhs: Integer) {
        self.rem_floor_from(&lhs);
    }
    #[inline]
    fn div_euc_from(&mut self, lhs: Integer) {
        self.div_euc_from(&lhs);
    }
    #[inline]
    fn rem_euc_from(&mut self, lhs: Integer) {
        self.rem_euc_from(&lhs);
    }
}

impl<'a> DivRemRoundingFrom<&'a Integer> for Integer {
    #[inline]
    fn div_trunc_from(&mut self, lhs: &'a Integer) {
        self.div_from(lhs);
    }
    #[inline]
    fn rem_trunc_from(&mut self, lhs: &'a Integer) {
        self.rem_from(lhs);
    }
    #[inline]
    fn div_ceil_from(&mut self, lhs: &'a Integer) {
        unsafe {
            xgmp::mpz_cdiv_q_check_0(
                self.inner_mut(),
                lhs.inner(),
                self.inner(),
            );
        }
    }
    #[inline]
    fn rem_ceil_from(&mut self, lhs: &'a Integer) {
        unsafe {
            xgmp::mpz_cdiv_r_check_0(
                self.inner_mut(),
                lhs.inner(),
                self.inner(),
            );
        }
    }
    #[inline]
    fn div_floor_from(&mut self, lhs: &'a Integer) {
        unsafe {
            xgmp::mpz_fdiv_q_check_0(
                self.inner_mut(),
                lhs.inner(),
                self.inner(),
            );
        }
    }
    #[inline]
    fn rem_floor_from(&mut self, lhs: &'a Integer) {
        unsafe {
            xgmp::mpz_fdiv_r_check_0(
                self.inner_mut(),
                lhs.inner(),
                self.inner(),
            );
        }
    }
    #[inline]
    fn div_euc_from(&mut self, lhs: &'a Integer) {
        if self.cmp0() == Ordering::Greater {
            self.div_floor_from(lhs);
        } else {
            self.div_ceil_from(lhs);
        }
    }
    #[inline]
    fn rem_euc_from(&mut self, lhs: &'a Integer) {
        if self.cmp0() == Ordering::Greater {
            self.rem_floor_from(lhs);
        } else {
            self.rem_ceil_from(lhs);
        }
    }
}

impl<'a> DivRemRounding<&'a Integer> for &'a Integer {
    type DivOutput = DivRemRoundingRef<'a>;
    type RemOutput = DivRemRoundingRef<'a>;
    #[inline]
    fn div_trunc(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::DivTrunc(self, rhs)
    }
    #[inline]
    fn rem_trunc(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::RemTrunc(self, rhs)
    }
    #[inline]
    fn div_ceil(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::DivCeil(self, rhs)
    }
    #[inline]
    fn rem_ceil(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::RemCeil(self, rhs)
    }
    #[inline]
    fn div_floor(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::DivFloor(self, rhs)
    }
    #[inline]
    fn rem_floor(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::RemFloor(self, rhs)
    }
    #[inline]
    fn div_euc(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::DivEuc(self, rhs)
    }
    #[inline]
    fn rem_euc(self, rhs: &'a Integer) -> DivRemRoundingRef {
        DivRemRoundingRef::RemEuc(self, rhs)
    }
}

#[derive(Clone, Copy)]
pub enum DivRemRoundingRef<'a> {
    DivTrunc(&'a Integer, &'a Integer),
    RemTrunc(&'a Integer, &'a Integer),
    DivCeil(&'a Integer, &'a Integer),
    RemCeil(&'a Integer, &'a Integer),
    DivFloor(&'a Integer, &'a Integer),
    RemFloor(&'a Integer, &'a Integer),
    DivEuc(&'a Integer, &'a Integer),
    RemEuc(&'a Integer, &'a Integer),
}

from_borrow! { DivRemRoundingRef<'a> => Integer }

impl<'a> Assign<DivRemRoundingRef<'a>> for Integer {
    #[inline]
    fn assign(&mut self, src: DivRemRoundingRef) {
        use self::DivRemRoundingRef::*;
        match src {
            DivTrunc(lhs, rhs) => unsafe {
                xgmp::mpz_tdiv_q_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            RemTrunc(lhs, rhs) => unsafe {
                xgmp::mpz_tdiv_r_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            DivCeil(lhs, rhs) => unsafe {
                xgmp::mpz_cdiv_q_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            RemCeil(lhs, rhs) => unsafe {
                xgmp::mpz_cdiv_r_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            DivFloor(lhs, rhs) => unsafe {
                xgmp::mpz_fdiv_q_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            RemFloor(lhs, rhs) => unsafe {
                xgmp::mpz_fdiv_r_check_0(
                    self.inner_mut(),
                    lhs.inner(),
                    rhs.inner(),
                );
            },
            DivEuc(lhs, rhs) => if rhs.cmp0() == Ordering::Greater {
                self.assign(DivFloor(lhs, rhs));
            } else {
                self.assign(DivCeil(lhs, rhs));
            },
            RemEuc(lhs, rhs) => if rhs.cmp0() == Ordering::Greater {
                self.assign(RemFloor(lhs, rhs));
            } else {
                self.assign(RemCeil(lhs, rhs));
            },
        }
    }
}
