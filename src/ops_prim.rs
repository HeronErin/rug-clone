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

use Assign;
use ops::{AddFrom, BitAndFrom, BitOrFrom, BitXorFrom, DivFrom, DivRounding,
          DivRoundingAssign, DivRoundingFrom, MulFrom, NegAssign, NotAssign,
          Pow, PowAssign, PowFrom, RemFrom, RemRounding, RemRoundingAssign,
          RemRoundingFrom, ShlFrom, ShrFrom, SubFrom};
use std::borrow::Cow;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

macro_rules! assign_from {
    { $T:ty; $op:ident; $Imp:ident $method:ident } => {
        impl $Imp for $T {
            #[inline]
            fn $method(&mut self, lhs: $T) {
                *self = lhs.$op(*self);
            }
        }
        impl<'a> $Imp<&'a $T> for $T {
            #[inline]
            fn $method(&mut self, lhs: &'a $T) {
                *self = (*lhs).$op(*self);
            }
        }
    }
}
macro_rules! int_ops {
    { $($T:ty)* } => {
        $(
            impl Assign for $T {
                #[inline]
                fn assign(&mut self, src: $T) {
                    *self = src;
                }
            }
            impl<'a> Assign<&'a $T> for $T {
                #[inline]
                fn assign(&mut self, src: &'a $T) {
                    *self = *src;
                }
            }
            impl NotAssign for $T {
                #[inline]
                fn not_assign(&mut self) {
                    *self = !*self;
                }
            }
            impl Pow<u32> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: u32) -> $T {
                    self.pow(rhs)
                }
            }
            impl<'a> Pow<u32> for &'a $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: u32) -> $T {
                    (*self).pow(rhs)
                }
            }
            impl<'a> Pow<&'a u32> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a u32) -> $T {
                    self.pow(*rhs)
                }
            }
            impl<'a, 'b> Pow<&'a u32> for &'b $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a u32) -> $T {
                    (*self).pow(*rhs)
                }
            }
            impl PowAssign<u32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: u32) {
                    *self = self.pow(rhs);
                }
            }
            impl<'a> PowAssign<&'a u32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: &'a u32) {
                    *self = self.pow(*rhs);
                }
            }
            assign_from! { $T; add; AddFrom add_from }
            assign_from! { $T; sub; SubFrom sub_from }
            assign_from! { $T; mul; MulFrom mul_from }
            assign_from! { $T; div; DivFrom div_from }
            assign_from! { $T; rem; RemFrom rem_from }
            assign_from! { $T; bitand; BitAndFrom bitand_from }
            assign_from! { $T; bitor; BitOrFrom bitor_from }
            assign_from! { $T; bitxor; BitXorFrom bitxor_from }
            assign_from! { $T; shl; ShlFrom shl_from }
            assign_from! { $T; shr; ShrFrom shr_from }
        )*
    }
}
macro_rules! int_neg {
    { $($T:ty)* } => {
        $(
            impl NegAssign for $T {
                #[inline]
                fn neg_assign(&mut self) {
                    *self = -*self;
                }
            }
        )*
    }
}
macro_rules! float_ops {
    { $($T:ty)* } => {
        $(
            impl Assign for $T {
                #[inline]
                fn assign(&mut self, src: $T) {
                    *self = src;
                }
            }
            impl<'a> Assign<&'a $T> for $T {
                #[inline]
                fn assign(&mut self, src: &'a $T) {
                    *self = *src;
                }
            }
            impl Pow<i32> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: i32) -> $T {
                    self.powi(rhs)
                }
            }
            impl<'a> Pow<i32> for &'a $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: i32) -> $T {
                    self.powi(rhs)
                }
            }
            impl<'a> Pow<&'a i32> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a i32) -> $T {
                    self.powi(*rhs)
                }
            }
            impl<'a, 'b> Pow<&'a i32> for &'b $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a i32) -> $T {
                    self.powi(*rhs)
                }
            }
            impl PowAssign<i32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: i32) {
                    *self = self.powi(rhs);
                }
            }
            impl<'a> PowAssign<&'a i32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: &'a i32) {
                    *self = self.powi(*rhs);
                }
            }
            impl Pow<$T> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: $T) -> $T {
                    self.powf(rhs)
                }
            }
            impl<'a> Pow<$T> for &'a $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: $T) -> $T {
                    self.powf(rhs)
                }
            }
            impl<'a> Pow<&'a $T> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a $T) -> $T {
                    self.powf(*rhs)
                }
            }
            impl<'a, 'b> Pow<&'a $T> for &'b $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: &'a $T) -> $T {
                    self.powf(*rhs)
                }
            }
            impl PowAssign<$T> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: $T) {
                    *self = self.powf(rhs);
                }
            }
            impl<'a> PowAssign<&'a $T> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: &'a $T) {
                    *self = self.powf(*rhs);
                }
            }
            assign_from!{ $T; add; AddFrom add_from }
            assign_from!{ $T; sub; SubFrom sub_from }
            assign_from!{ $T; mul; MulFrom mul_from }
            assign_from!{ $T; div; DivFrom div_from }
            assign_from!{ $T; pow; PowFrom pow_from }
        )*
    }
}

macro_rules! div_signed {
    { $($T:ty)* } => {
        $(
            impl DivRounding for $T {
                type Output = $T;
                #[inline]
                fn div_trunc(self, rhs: $T) -> $T {
                    self / rhs
                }
                #[inline]
                fn div_ceil(self, rhs: $T) -> $T {
                    let (q, r) = (self / rhs, self % rhs);
                    let change = if rhs > 0 { r > 0 } else { r < 0 };
                    if change {
                        q + 1
                    } else {
                        q
                    }
                }
                #[inline]
                fn div_floor(self, rhs: $T) -> $T {
                    let (q, r) = (self / rhs, self % rhs);
                    let change = if rhs > 0 { r < 0 } else { r > 0 };
                    if change {
                        q - 1
                    } else {
                        q
                    }
                }
                #[inline]
                fn div_euc(self, rhs: $T) -> $T {
                    let (q, r) = (self / rhs, self % rhs);
                    if r < 0 {
                        if rhs < 0 {
                            q + 1
                        } else {
                            q - 1
                        }
                    } else {
                        q
                    }
                }
            }

            impl<'a> DivRounding<&'a $T> for $T {
                type Output = $T;
                #[inline]
                fn div_trunc(self, rhs: &'a $T) -> $T {
                    <$T as DivRounding>::div_trunc(self, *rhs)
                }
                #[inline]
                fn div_ceil(self, rhs: &'a $T) -> $T {
                    <$T as DivRounding>::div_ceil(self, *rhs)
                }
                #[inline]
                fn div_floor(self, rhs: &'a $T) -> $T {
                    <$T as DivRounding>::div_floor(self, *rhs)
                }
                #[inline]
                fn div_euc(self, rhs: &'a $T) -> $T {
                    <$T as DivRounding>::div_euc(self, *rhs)
                }
            }

            impl RemRounding for $T {
                type Output = $T;
                #[inline]
                fn rem_trunc(self, rhs: $T) -> $T {
                    self % rhs
                }
                #[inline]
                fn rem_ceil(self, rhs: $T) -> $T {
                    let r = self % rhs;
                    let change = if rhs > 0 { r > 0 } else { r < 0 };
                    if change {
                        r - rhs
                    } else {
                        r
                    }
                }
                #[inline]
                fn rem_floor(self, rhs: $T) -> $T {
                    let r = self % rhs;
                    let change = if rhs > 0 { r < 0 } else { r > 0 };
                    if change {
                        r + rhs
                    } else {
                        r
                    }
                }
                #[inline]
                fn rem_euc(self, rhs: $T) -> $T {
                    let r = self % rhs;
                    if r < 0 {
                        if rhs < 0 {
                            r - rhs
                        } else {
                            r + rhs
                        }
                    } else {
                        r
                    }
                }
            }

            impl<'a> RemRounding<&'a $T> for $T {
                type Output = $T;
                #[inline]
                fn rem_trunc(self, rhs: &'a $T) -> $T {
                    <$T as RemRounding>::rem_trunc(self, *rhs)
                }
                #[inline]
                fn rem_ceil(self, rhs: &'a $T) -> $T {
                    <$T as RemRounding>::rem_ceil(self, *rhs)
                }
                #[inline]
                fn rem_floor(self, rhs: &'a $T) -> $T {
                    <$T as RemRounding>::rem_floor(self, *rhs)
                }
                #[inline]
                fn rem_euc(self, rhs: &'a $T) -> $T {
                    <$T as RemRounding>::rem_euc(self, *rhs)
                }
            }

            impl DivRoundingAssign for $T {
                #[inline]
                fn div_trunc_assign(&mut self, rhs: $T) {
                    *self = <$T as DivRounding>::div_trunc(*self, rhs);
                }
                #[inline]
                fn div_ceil_assign(&mut self, rhs: $T) {
                    *self = <$T as DivRounding>::div_ceil(*self, rhs);
                }
                #[inline]
                fn div_floor_assign(&mut self, rhs: $T) {
                    *self = <$T as DivRounding>::div_floor(*self, rhs);
                }
                #[inline]
                fn div_euc_assign(&mut self, rhs: $T) {
                    *self = <$T as DivRounding>::div_euc(*self, rhs);
                }
            }

            impl<'a> DivRoundingAssign<&'a $T> for $T {
                #[inline]
                fn div_trunc_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as DivRounding>::div_trunc(*self, *rhs);
                }
                #[inline]
                fn div_ceil_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as DivRounding>::div_ceil(*self, *rhs);
                }
                #[inline]
                fn div_floor_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as DivRounding>::div_floor(*self, *rhs);
                }
                #[inline]
                fn div_euc_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as DivRounding>::div_euc(*self, *rhs);
                }
            }

            impl DivRoundingFrom for $T {
                #[inline]
                fn div_trunc_from(&mut self, lhs: $T) {
                    *self = <$T as DivRounding>::div_trunc(lhs, *self);
                }
                #[inline]
                fn div_ceil_from(&mut self, lhs: $T) {
                    *self = <$T as DivRounding>::div_ceil(lhs, *self);
                }
                #[inline]
                fn div_floor_from(&mut self, lhs: $T) {
                    *self = <$T as DivRounding>::div_floor(lhs, *self);
                }
                #[inline]
                fn div_euc_from(&mut self, lhs: $T) {
                    *self = <$T as DivRounding>::div_euc(lhs, *self);
                }
            }

            impl<'a> DivRoundingFrom<&'a $T> for $T {
                #[inline]
                fn div_trunc_from(&mut self, lhs: &'a $T) {
                    *self = <$T as DivRounding>::div_trunc(*lhs, *self);
                }
                #[inline]
                fn div_ceil_from(&mut self, lhs: &'a $T) {
                    *self = <$T as DivRounding>::div_ceil(*lhs, *self);
                }
                #[inline]
                fn div_floor_from(&mut self, lhs: &'a $T) {
                    *self = <$T as DivRounding>::div_floor(*lhs, *self);
                }
                #[inline]
                fn div_euc_from(&mut self, lhs: &'a $T) {
                    *self = <$T as DivRounding>::div_euc(*lhs, *self);
                }
            }

            impl RemRoundingAssign for $T {
                #[inline]
                fn rem_trunc_assign(&mut self, rhs: $T) {
                    *self = <$T as RemRounding>::rem_trunc(*self, rhs);
                }
                #[inline]
                fn rem_ceil_assign(&mut self, rhs: $T) {
                    *self = <$T as RemRounding>::rem_ceil(*self, rhs);
                }
                #[inline]
                fn rem_floor_assign(&mut self, rhs: $T) {
                    *self = <$T as RemRounding>::rem_floor(*self, rhs);
                }
                #[inline]
                fn rem_euc_assign(&mut self, rhs: $T) {
                    *self = <$T as RemRounding>::rem_euc(*self, rhs);
                }
            }

            impl<'a> RemRoundingAssign<&'a $T> for $T {
                #[inline]
                fn rem_trunc_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_trunc(*self, *rhs);
                }
                #[inline]
                fn rem_ceil_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_ceil(*self, *rhs);
                }
                #[inline]
                fn rem_floor_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_floor(*self, *rhs);
                }
                #[inline]
                fn rem_euc_assign(&mut self, rhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_euc(*self, *rhs);
                }
            }

            impl RemRoundingFrom for $T {
                #[inline]
                fn rem_trunc_from(&mut self, lhs: $T) {
                    *self = <$T as RemRounding>::rem_trunc(lhs, *self);
                }
                #[inline]
                fn rem_ceil_from(&mut self, lhs: $T) {
                    *self = <$T as RemRounding>::rem_ceil(lhs, *self);
                }
                #[inline]
                fn rem_floor_from(&mut self, lhs: $T) {
                    *self = <$T as RemRounding>::rem_floor(lhs, *self);
                }
                #[inline]
                fn rem_euc_from(&mut self, lhs: $T) {
                    *self = <$T as RemRounding>::rem_euc(lhs, *self);
                }
            }

            impl<'a> RemRoundingFrom<&'a $T> for $T {
                #[inline]
                fn rem_trunc_from(&mut self, lhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_trunc(*lhs, *self);
                }
                #[inline]
                fn rem_ceil_from(&mut self, lhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_ceil(*lhs, *self);
                }
                #[inline]
                fn rem_floor_from(&mut self, lhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_floor(*lhs, *self);
                }
                #[inline]
                fn rem_euc_from(&mut self, lhs: &'a $T) {
                    *self = <$T as RemRounding>::rem_euc(*lhs, *self);
                }
            }
        )*
    }
}

int_ops!{ i8 i16 i32 i64 isize u8 u16 u32 u64 usize }
int_neg!{ i8 i16 i32 i64 isize }
assign_from! { u32; pow; PowFrom pow_from }
float_ops!{ f32 f64 }

// DivRounding and RemRounding are not implemented for unsigned
// primitives, as the only methods different from standard truncating
// division is div_ceil and rem_ceil, and rem_ceil for unsigned
// operands can be less than zero, so it cannot be stored in unsigned.
div_signed!{ i8 i16 i32 i64 isize }

impl<'a> AddFrom<&'a str> for String {
    #[inline]
    fn add_from(&mut self, lhs: &str) {
        self.insert_str(0, lhs);
    }
}

impl<'a> AddFrom<&'a str> for Cow<'a, str> {
    fn add_from(&mut self, lhs: &'a str) {
        if lhs.is_empty() {
        } else if self.is_empty() {
            *self = Cow::Borrowed(lhs)
        } else {
            match *self {
                Cow::Borrowed(rhs) => {
                    let mut s = String::with_capacity(lhs.len() + rhs.len());
                    s.push_str(lhs);
                    s.push_str(rhs);
                    *self = Cow::Owned(s);
                }
                Cow::Owned(ref mut s) => {
                    s.insert_str(0, lhs);
                }
            }
        }
    }
}

impl<'a> AddFrom<Cow<'a, str>> for Cow<'a, str> {
    fn add_from(&mut self, lhs: Cow<'a, str>) {
        if lhs.is_empty() {
        } else if self.is_empty() {
            *self = lhs;
        } else {
            match *self {
                Cow::Borrowed(rhs) => {
                    let mut s = String::with_capacity(lhs.len() + rhs.len());
                    s.push_str(&lhs);
                    s.push_str(rhs);
                    *self = Cow::Owned(s);
                }
                Cow::Owned(ref mut s) => {
                    s.insert_str(0, &lhs);
                }
            }
        }
    }
}
