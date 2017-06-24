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

//! Operations on numbers.
//!
//! See the documentation for each trait method to see a usage
//! example.

use Assign;

/// Compound negation and assignment.
///
/// # Examples
///
/// ```rust
/// use rug::ops::NegAssign;
/// struct I(i32);
/// impl NegAssign for I {
///     fn neg_assign(&mut self) {
///         self.0 = -self.0;
///     }
/// }
/// let mut i = I(42);
/// i.neg_assign();
/// assert_eq!(i.0, -42);
/// ```
pub trait NegAssign {
    /// Peforms the negation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::NegAssign;
    /// let mut i = Integer::from(-42);
    /// i.neg_assign();
    /// assert_eq!(i, 42);
    /// # }
    /// ```
    fn neg_assign(&mut self);
}

/// Compound bitwise complement and assignement.
///
/// # Examples
///
/// ```rust
/// use rug::ops::NotAssign;
/// struct I(i32);
/// impl NotAssign for I {
///     fn not_assign(&mut self) {
///         self.0 = !self.0;
///     }
/// }
/// let mut i = I(42);
/// i.not_assign();
/// assert_eq!(i.0, !42);
/// ```
pub trait NotAssign {
    /// Peforms the complement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::NotAssign;
    /// let mut i = Integer::from(-42);
    /// i.not_assign();
    /// assert_eq!(i, !-42);
    /// # }
    /// ```
    fn not_assign(&mut self);
}

/// Compound addition and assignment to the rhs operand.
///
/// `rhs.add_from_assign(lhs)` has the same effect as
/// `rhs = lhs + rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::AddFromAssign;
/// struct S(String);
/// impl<'a> AddFromAssign<&'a str> for S {
///     fn add_from_assign(&mut self, lhs: &str) {
///         self.0.insert_str(0, lhs);
///     }
/// }
/// let mut s = S("world!".into());
/// s.add_from_assign("Hello, ");
/// assert_eq!(s.0, "Hello, world!");
/// ```
pub trait AddFromAssign<Lhs = Self> {
    /// Peforms the addition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::AddFromAssign;
    /// let mut rhs = Integer::from(10);
    /// rhs.add_from_assign(100);
    /// // rhs = 100 + 10
    /// assert_eq!(rhs, 110);
    /// # }
    /// ```
    fn add_from_assign(&mut self, lhs: Lhs);
}

/// Compound subtraction and assignment to the rhs operand.
///
/// `rhs.sub_from_assign(lhs)` has the same effect as
/// `rhs = lhs - rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::SubFromAssign;
/// struct I(i32);
/// impl SubFromAssign<i32> for I {
///     fn sub_from_assign(&mut self, lhs: i32) {
///         self.0 = lhs - self.0;
///     }
/// }
/// let mut i = I(10);
/// i.sub_from_assign(42);
/// assert_eq!(i.0, 32);
/// ```
pub trait SubFromAssign<Lhs = Self> {
    /// Peforms the subtraction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::SubFromAssign;
    /// let mut rhs = Integer::from(10);
    /// rhs.sub_from_assign(100);
    /// // rhs = 100 - 10
    /// assert_eq!(rhs, 90);
    /// # }
    /// ```
    fn sub_from_assign(&mut self, lhs: Lhs);
}

/// Compound multiplication and assignment to the rhs operand.
///
/// `rhs.mul_from_assign(lhs)` has the same effect as
/// `rhs = lhs * rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::MulFromAssign;
/// struct ColumnVec(i32, i32);
/// struct SquareMatrix(ColumnVec, ColumnVec);
/// impl<'a> MulFromAssign<&'a SquareMatrix> for ColumnVec {
///     fn mul_from_assign(&mut self, lhs: &SquareMatrix) {
///         let SquareMatrix(ref left, ref right) = *lhs;
///         let out_0 = left.0 * self.0 + right.0 * self.1;
///         self.1 = left.1 * self.0 + right.1 * self.1;
///         self.0 = out_0;
///     }
/// }
/// let mut col = ColumnVec(2, 30);
/// let matrix_left = ColumnVec(1, -2);
/// let matrix_right = ColumnVec(3, -1);
/// let matrix = SquareMatrix(matrix_left, matrix_right);
/// // ( 1   3) ( 2) = ( 92)
/// // (-2  -1) (30)   (-34)
/// col.mul_from_assign(&matrix);
/// assert_eq!(col.0, 92);
/// assert_eq!(col.1, -34);
/// ```
pub trait MulFromAssign<Lhs = Self> {
    /// Peforms the multiplication.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::MulFromAssign;
    /// let mut rhs = Integer::from(5);
    /// rhs.mul_from_assign(50);
    /// // rhs = 50 * 5
    /// assert_eq!(rhs, 250);
    /// # }
    /// ```
    fn mul_from_assign(&mut self, lhs: Lhs);
}

/// Compound division and assignment to the rhs operand.
///
/// `rhs.div_from_assign(lhs)` has the same effect as
/// `rhs = lhs / rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::DivFromAssign;
/// struct I(i32);
/// impl DivFromAssign<i32> for I {
///     fn div_from_assign(&mut self, lhs: i32) {
///         self.0 = lhs / self.0;
///     }
/// }
/// let mut i = I(10);
/// i.div_from_assign(42);
/// assert_eq!(i.0, 4);
/// ```
pub trait DivFromAssign<Lhs = Self> {
    /// Peforms the division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::DivFromAssign;
    /// let mut rhs = Integer::from(5);
    /// rhs.div_from_assign(50);
    /// // rhs = 50 / 5
    /// assert_eq!(rhs, 10);
    /// # }
    /// ```
    fn div_from_assign(&mut self, lhs: Lhs);
}

/// Compound remainder operation and assignment to the rhs operand.
///
/// `rhs.rem_from_assign(lhs)` has the same effect as
/// `rhs = lhs % rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::RemFromAssign;
/// struct I(i32);
/// impl RemFromAssign<i32> for I {
///     fn rem_from_assign(&mut self, lhs: i32) {
///         self.0 = lhs % self.0;
///     }
/// }
/// let mut i = I(10);
/// i.rem_from_assign(42);
/// assert_eq!(i.0, 2);
/// ```
pub trait RemFromAssign<Lhs = Self> {
    /// Peforms the remainder operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::RemFromAssign;
    /// let mut rhs = Integer::from(2);
    /// rhs.rem_from_assign(17);
    /// // rhs = 17 / 2
    /// assert_eq!(rhs, 1);
    /// # }
    /// ```
    fn rem_from_assign(&mut self, lhs: Lhs);
}

/// Compound bitwise AND and assignment to the rhs operand.
///
/// `rhs.bitand_from_assign(lhs)` has the same effect as
/// `rhs = lhs & rhs`.
pub trait BitAndFromAssign<Lhs = Self> {
    /// Peforms the AND operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitAndFromAssign;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitand_from_assign(0x33);
    /// // rhs = 0x33 & 0xf0
    /// assert_eq!(rhs, 0x30);
    /// # }
    /// ```
    fn bitand_from_assign(&mut self, lhs: Lhs);
}

/// Compound bitwise OR and assignment to the rhs operand.
///
/// `rhs.bitor_from_assign(lhs)` has the same effect as
/// `rhs = lhs | rhs`.
pub trait BitOrFromAssign<Lhs = Self> {
    /// Peforms the OR operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitOrFromAssign;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitor_from_assign(0x33);
    /// // rhs = 0x33 | 0xf0
    /// assert_eq!(rhs, 0xf3);
    /// # }
    /// ```
    fn bitor_from_assign(&mut self, lhs: Lhs);
}

/// Compound bitwise XOR and assignment to the rhs operand.
///
/// `rhs.bitxor_from_assign(lhs)` has the same effect as
/// `rhs = lhs ^ rhs`.
pub trait BitXorFromAssign<Lhs = Self> {
    /// Peforms the XOR operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitXorFromAssign;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitxor_from_assign(0x33);
    /// // rhs = 0x33 ^ 0xf0
    /// assert_eq!(rhs, 0xc3);
    /// # }
    /// ```
    fn bitxor_from_assign(&mut self, lhs: Lhs);
}

/// The power operation.
///
/// # Examples
///
/// ```rust
/// use rug::ops::Pow;
/// struct U(u32);
/// impl Pow<u16> for U {
///     type Output = u32;
///     fn pow(self, rhs: u16) -> u32 {
///         self.0.pow(rhs as u32)
///     }
/// }
/// let u = U(5);
/// assert_eq!(u.pow(2_u16), 25);
/// ```
pub trait Pow<Rhs = Self> {
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::Pow;
    /// let base = Integer::from(10);
    /// let ans = base.pow(5);
    /// assert_eq!(ans, 100_000);
    /// # }
    /// ```
    fn pow(self, rhs: Rhs) -> Self::Output;
}

/// Compound power operation and assignment.
///
/// # Examples
///
/// ```rust
/// use rug::ops::PowAssign;
/// struct U(u32);
/// impl PowAssign<u16> for U {
///     fn pow_assign(&mut self, rhs: u16) {
///         self.0 = self.0.pow(rhs as u32);
///     }
/// }
/// let mut u = U(5);
/// u.pow_assign(2_u16);
/// assert_eq!(u.0, 25);
/// ```
pub trait PowAssign<Rhs = Self> {
    /// Peforms the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::PowAssign;
    /// let mut i = Integer::from(10);
    /// i.pow_assign(5);
    /// assert_eq!(i, 100_000);
    /// # }
    /// ```
    fn pow_assign(&mut self, rhs: Rhs);
}

/// Compound power operation and assignment to the rhs operand.
///
/// `rhs.pow_from_assign(lhs)` has the same effect as
/// `rhs = lhs.pow(rhs)`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::PowFromAssign;
/// struct U(u32);
/// impl PowFromAssign<u32> for U {
///     fn pow_from_assign(&mut self, lhs: u32) {
///         self.0 = lhs.pow(self.0);
///     }
/// }
/// let mut u = U(2);
/// u.pow_from_assign(5);
/// assert_eq!(u.0, 25);
/// ```
pub trait PowFromAssign<Lhs = Self> {
    /// Peforms the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::ops::PowFromAssign;
    /// let mut rhs = Float::with_val(53, 5);
    /// rhs.pow_from_assign(10);
    /// // rhs = 10 ** 5
    /// assert_eq!(rhs, 100_000);
    /// # }
    /// ```
    fn pow_from_assign(&mut self, lhs: Lhs);
}

/// Compound addition and assignment with a specified rounding method.
pub trait AddRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the addition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::AddRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.add_round(-0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn add_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Compound addition and assignment to the rhs operand with a
/// specified rounding method.
pub trait AddFromRound<Lhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the addition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::AddFromRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -0.3);
    /// let dir = f.add_from_round(-3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn add_from_round(
        &mut self,
        lhs: Lhs,
        round: Self::Round,
    ) -> Self::Ordering;
}

/// Compound subtraction and assignment with a specified rounding
/// method.
pub trait SubRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the subtraction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::SubRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.sub_round(0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn sub_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Compound subtraction and assignment to the rhs operand with a
/// specified rounding method.
pub trait SubFromRound<Lhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the subtraction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::SubFromRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, 0.3);
    /// let dir = f.sub_from_round(-3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn sub_from_round(
        &mut self,
        lhs: Lhs,
        round: Self::Round,
    ) -> Self::Ordering;
}

/// Compound multiplication and assignment with a specified rounding
/// method.
pub trait MulRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the multiplication.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::MulRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.mul_round(13, Round::Nearest);
    /// // -39 rounded down to -40
    /// assert_eq!(f, -40);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn mul_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Compound multiplication and assignment to the rhs operand with a
/// specified rounding method.
pub trait MulFromRound<Lhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the multiplication.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::MulFromRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, 13);
    /// let dir = f.mul_from_round(-3, Round::Nearest);
    /// // -39 rounded down to -40
    /// assert_eq!(f, -40);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn mul_from_round(
        &mut self,
        rhs: Lhs,
        round: Self::Round,
    ) -> Self::Ordering;
}

/// Compound division and assignment with a specified rounding method.
pub trait DivRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::DivRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.div_round(5, Round::Nearest);
    /// // -0.6 rounded down to -0.625
    /// assert_eq!(f, -0.625);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn div_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Compound division and assignment to the rhs operand with a
/// specified rounding method.
pub trait DivFromRound<Lhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::DivFromRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, 5);
    /// let dir = f.div_from_round(-3, Round::Nearest);
    /// // -0.6 rounded down to -0.625
    /// assert_eq!(f, -0.625);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn div_from_round(
        &mut self,
        rhs: Lhs,
        round: Self::Round,
    ) -> Self::Ordering;
}

/// Compound power operation and assignment with a specified rounding
/// method.
pub trait PowRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::PowRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.pow_round(5, Round::Nearest);
    /// // -243 rounded up to -240
    /// assert_eq!(f, -240);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn pow_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Compound power operation and assignment to the rhs operand with a
/// specified rounding method.
pub trait PowFromRound<Lhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::float::Round;
    /// use rug::ops::PowFromRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, 5);
    /// let dir = f.pow_from_round(-3, Round::Nearest);
    /// // -243 rounded up to -240
    /// assert_eq!(f, -240);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn pow_from_round(
        &mut self,
        rhs: Lhs,
        round: Self::Round,
    ) -> Self::Ordering;
}

macro_rules! from_assign {
    { $T:ty; $op:ident; $Imp:ident $method:ident } => {
        impl $Imp for $T {
            #[inline]
            fn $method(&mut self, lhs: $T) {
                *self = lhs.$op(*self);
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
            impl PowAssign<u32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: u32) {
                    *self = self.pow(rhs);
                }
            }
            from_assign! { $T; add; AddFromAssign add_from_assign }
            from_assign! { $T; sub; SubFromAssign sub_from_assign }
            from_assign! { $T; mul; MulFromAssign mul_from_assign }
            from_assign! { $T; div; DivFromAssign div_from_assign }
            from_assign! { $T; rem; RemFromAssign rem_from_assign }
            from_assign! { $T; bitand; BitAndFromAssign bitand_from_assign }
            from_assign! { $T; bitor; BitOrFromAssign bitor_from_assign }
            from_assign! { $T; bitxor; BitXorFromAssign bitxor_from_assign }
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
            impl Pow<i32> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: i32) -> $T {
                    self.powi(rhs)
                }
            }
            impl PowAssign<i32> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: i32) {
                    *self = self.powi(rhs);
                }
            }
            impl Pow for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: $T) -> $T {
                    self.powf(rhs)
                }
            }
            impl PowAssign for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: $T) {
                    *self = self.powf(rhs);
                }
            }
            from_assign!{ $T; add; AddFromAssign add_from_assign }
            from_assign!{ $T; sub; SubFromAssign sub_from_assign }
            from_assign!{ $T; mul; MulFromAssign mul_from_assign }
            from_assign!{ $T; div; DivFromAssign div_from_assign }
            from_assign!{ $T; pow; PowFromAssign pow_from_assign }
        )*
    }
}

use std::borrow::Cow;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Sub};
int_ops!{ i8 i16 i32 i64 u8 u16 u32 u64 }
int_neg!{ i8 i16 i32 i64 }
from_assign! { u32; pow; PowFromAssign pow_from_assign }
float_ops!{ f32 f64 }

impl<'a> AddFromAssign<&'a str> for String {
    #[inline]
    fn add_from_assign(&mut self, lhs: &str) {
        self.insert_str(0, lhs);
    }
}

impl<'a> AddFromAssign<&'a str> for Cow<'a, str> {
    fn add_from_assign(&mut self, lhs: &'a str) {
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

impl<'a> AddFromAssign<Cow<'a, str>> for Cow<'a, str> {
    fn add_from_assign(&mut self, lhs: Cow<'a, str>) {
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
