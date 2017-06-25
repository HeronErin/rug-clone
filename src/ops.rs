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
/// `rhs.add_from(lhs)` has the same effect as `rhs = lhs + rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::AddFrom;
/// struct S(String);
/// impl<'a> AddFrom<&'a str> for S {
///     fn add_from(&mut self, lhs: &str) {
///         self.0.insert_str(0, lhs);
///     }
/// }
/// let mut s = S("world!".into());
/// s.add_from("Hello, ");
/// assert_eq!(s.0, "Hello, world!");
/// ```
pub trait AddFrom<Lhs = Self> {
    /// Peforms the addition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::AddFrom;
    /// let mut rhs = Integer::from(10);
    /// rhs.add_from(100);
    /// // rhs = 100 + 10
    /// assert_eq!(rhs, 110);
    /// # }
    /// ```
    fn add_from(&mut self, lhs: Lhs);
}

/// Compound subtraction and assignment to the rhs operand.
///
/// `rhs.sub_from(lhs)` has the same effect as `rhs = lhs - rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::SubFrom;
/// struct I(i32);
/// impl SubFrom<i32> for I {
///     fn sub_from(&mut self, lhs: i32) {
///         self.0 = lhs - self.0;
///     }
/// }
/// let mut i = I(10);
/// i.sub_from(42);
/// assert_eq!(i.0, 32);
/// ```
pub trait SubFrom<Lhs = Self> {
    /// Peforms the subtraction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::SubFrom;
    /// let mut rhs = Integer::from(10);
    /// rhs.sub_from(100);
    /// // rhs = 100 - 10
    /// assert_eq!(rhs, 90);
    /// # }
    /// ```
    fn sub_from(&mut self, lhs: Lhs);
}

/// Compound multiplication and assignment to the rhs operand.
///
/// `rhs.mul_from(lhs)` has the same effect as `rhs = lhs * rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::MulFrom;
/// struct ColumnVec(i32, i32);
/// struct SquareMatrix(ColumnVec, ColumnVec);
/// impl<'a> MulFrom<&'a SquareMatrix> for ColumnVec {
///     fn mul_from(&mut self, lhs: &SquareMatrix) {
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
/// col.mul_from(&matrix);
/// assert_eq!(col.0, 92);
/// assert_eq!(col.1, -34);
/// ```
pub trait MulFrom<Lhs = Self> {
    /// Peforms the multiplication.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::MulFrom;
    /// let mut rhs = Integer::from(5);
    /// rhs.mul_from(50);
    /// // rhs = 50 * 5
    /// assert_eq!(rhs, 250);
    /// # }
    /// ```
    fn mul_from(&mut self, lhs: Lhs);
}

/// Compound division and assignment to the rhs operand.
///
/// `rhs.div_from(lhs)` has the same effect as `rhs = lhs / rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::DivFrom;
/// struct I(i32);
/// impl DivFrom<i32> for I {
///     fn div_from(&mut self, lhs: i32) {
///         self.0 = lhs / self.0;
///     }
/// }
/// let mut i = I(10);
/// i.div_from(42);
/// assert_eq!(i.0, 4);
/// ```
pub trait DivFrom<Lhs = Self> {
    /// Peforms the division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::DivFrom;
    /// let mut rhs = Integer::from(5);
    /// rhs.div_from(50);
    /// // rhs = 50 / 5
    /// assert_eq!(rhs, 10);
    /// # }
    /// ```
    fn div_from(&mut self, lhs: Lhs);
}

/// Compound remainder operation and assignment to the rhs operand.
///
/// `rhs.rem_from(lhs)` has the same effect as `rhs = lhs % rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::RemFrom;
/// struct I(i32);
/// impl RemFrom<i32> for I {
///     fn rem_from(&mut self, lhs: i32) {
///         self.0 = lhs % self.0;
///     }
/// }
/// let mut i = I(10);
/// i.rem_from(42);
/// assert_eq!(i.0, 2);
/// ```
pub trait RemFrom<Lhs = Self> {
    /// Peforms the remainder operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::RemFrom;
    /// let mut rhs = Integer::from(2);
    /// rhs.rem_from(17);
    /// // rhs = 17 / 2
    /// assert_eq!(rhs, 1);
    /// # }
    /// ```
    fn rem_from(&mut self, lhs: Lhs);
}

/// Compound bitwise AND and assignment to the rhs operand.
///
/// `rhs.bitand_from(lhs)` has the same effect as `rhs = lhs & rhs`.
pub trait BitAndFrom<Lhs = Self> {
    /// Peforms the AND operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitAndFrom;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitand_from(0x33);
    /// // rhs = 0x33 & 0xf0
    /// assert_eq!(rhs, 0x30);
    /// # }
    /// ```
    fn bitand_from(&mut self, lhs: Lhs);
}

/// Compound bitwise OR and assignment to the rhs operand.
///
/// `rhs.bitor_from(lhs)` has the same effect as `rhs = lhs | rhs`.
pub trait BitOrFrom<Lhs = Self> {
    /// Peforms the OR operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitOrFrom;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitor_from(0x33);
    /// // rhs = 0x33 | 0xf0
    /// assert_eq!(rhs, 0xf3);
    /// # }
    /// ```
    fn bitor_from(&mut self, lhs: Lhs);
}

/// Compound bitwise XOR and assignment to the rhs operand.
///
/// `rhs.bitxor_from(lhs)` has the same effect as `rhs = lhs ^ rhs`.
pub trait BitXorFrom<Lhs = Self> {
    /// Peforms the XOR operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::Integer;
    /// use rug::ops::BitXorFrom;
    /// let mut rhs = Integer::from(0xf0);
    /// rhs.bitxor_from(0x33);
    /// // rhs = 0x33 ^ 0xf0
    /// assert_eq!(rhs, 0xc3);
    /// # }
    /// ```
    fn bitxor_from(&mut self, lhs: Lhs);
}

/// Compound left shift and assignment to the rhs operand.
///
/// `rhs.shl_from(lhs)` has the same effect as `rhs = lhs << rhs`.
///
/// # Examples
///
/// ```rust
/// # #[cfg(feature = "integer")] {
/// use rug::Integer;
/// use rug::ops::ShlFrom;
/// use std::mem;
/// struct I(Integer);
/// impl ShlFrom for I {
///     fn shl_from(&mut self, mut lhs: I) {
///         let rhs = self.0.to_i32().expect("overflow");
///         mem::swap(self, &mut lhs);
///         self.0 <<= rhs;
///     }
/// }
/// let mut i = I(Integer::from(200));
/// i.shl_from(I(Integer::from(0xf000)));
/// let expected = Integer::from(0xf000) << 200;
/// assert_eq!(i.0, expected);
/// # }
/// ```
pub trait ShlFrom<Lhs = Self> {
    /// Peforms the left shift.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::ops::ShlFrom;
    /// let mut rhs = 4;
    /// rhs.shl_from(0x00f0);
    /// // rhs = 0x00f0 << 4
    /// assert_eq!(rhs, 0x0f00);
    /// ```
    fn shl_from(&mut self, lhs: Lhs);
}

/// Compound right shift and assignment to the rhs operand.
///
/// `rhs.shr_from(lhs)` has the same effect as `rhs = lhs >> rhs`.
///
/// # Examples
///
/// ```rust
/// # #[cfg(feature = "integer")] {
/// use rug::Integer;
/// use rug::ops::ShrFrom;
/// use std::mem;
/// struct I(Integer);
/// impl ShrFrom for I {
///     fn shr_from(&mut self, mut lhs: I) {
///         let rhs = self.0.to_i32().expect("overflow");
///         mem::swap(self, &mut lhs);
///         self.0 >>= rhs;
///     }
/// }
/// let mut i = I(Integer::from(4));
/// i.shr_from(I(Integer::from(0xf000)));
/// let expected = Integer::from(0xf000) >> 4;
/// assert_eq!(i.0, expected);
/// # }
/// ```
pub trait ShrFrom<Lhs = Self> {
    /// Peforms the right shift.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::ops::ShrFrom;
    /// let mut rhs = 4;
    /// rhs.shr_from(0x00f0);
    /// // rhs = 0x00f0 >> 4
    /// assert_eq!(rhs, 0x000f);
    /// ```
    fn shr_from(&mut self, lhs: Lhs);
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
pub trait Pow<Rhs> {
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
pub trait PowAssign<Rhs> {
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
/// `rhs.pow_from(lhs)` has the same effect as `rhs = lhs.pow(rhs)`.
///
/// # Examples
///
/// ```rust
/// use rug::ops::PowFrom;
/// struct U(u32);
/// impl PowFrom<u32> for U {
///     fn pow_from(&mut self, lhs: u32) {
///         self.0 = lhs.pow(self.0);
///     }
/// }
/// let mut u = U(2);
/// u.pow_from(5);
/// assert_eq!(u.0, 25);
/// ```
pub trait PowFrom<Lhs = Self> {
    /// Peforms the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::ops::PowFrom;
    /// let mut rhs = Float::with_val(53, 5);
    /// rhs.pow_from(10);
    /// // rhs = 10 ** 5
    /// assert_eq!(rhs, 100_000);
    /// # }
    /// ```
    fn pow_from(&mut self, lhs: Lhs);
}

/// Compound addition and assignment with a specified rounding method.
pub trait AddAssignRound<Rhs = Self> {
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
    /// use rug::ops::AddAssignRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.add_assign_round(-0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn add_assign_round(
        &mut self,
        rhs: Rhs,
        round: Self::Round,
    ) -> Self::Ordering;
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
pub trait SubAssignRound<Rhs = Self> {
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
    /// use rug::ops::SubAssignRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.sub_assign_round(0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn sub_assign_round(
        &mut self,
        rhs: Rhs,
        round: Self::Round,
    ) -> Self::Ordering;
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
pub trait MulAssignRound<Rhs = Self> {
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
    /// use rug::ops::MulAssignRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.mul_assign_round(13, Round::Nearest);
    /// // -39 rounded down to -40
    /// assert_eq!(f, -40);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn mul_assign_round(
        &mut self,
        rhs: Rhs,
        round: Self::Round,
    ) -> Self::Ordering;
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
pub trait DivAssignRound<Rhs = Self> {
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
    /// use rug::ops::DivAssignRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.div_assign_round(5, Round::Nearest);
    /// // -0.6 rounded down to -0.625
    /// assert_eq!(f, -0.625);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn div_assign_round(
        &mut self,
        rhs: Rhs,
        round: Self::Round,
    ) -> Self::Ordering;
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
pub trait PowAssignRound<Rhs = Self> {
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
    /// use rug::ops::PowAssignRound;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::with_val(4, -3);
    /// let dir = f.pow_assign_round(5, Round::Nearest);
    /// // -243 rounded up to -240
    /// assert_eq!(f, -240);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn pow_assign_round(
        &mut self,
        rhs: Rhs,
        round: Self::Round,
    ) -> Self::Ordering;
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

macro_rules! assign_from {
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
            impl Pow<$T> for $T {
                type Output = $T;
                #[inline]
                fn pow(self, rhs: $T) -> $T {
                    self.powf(rhs)
                }
            }
            impl PowAssign<$T> for $T {
                #[inline]
                fn pow_assign(&mut self, rhs: $T) {
                    *self = self.powf(rhs);
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

use std::borrow::Cow;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};
int_ops!{ i8 i16 i32 i64 isize u8 u16 u32 u64 usize }
int_neg!{ i8 i16 i32 i64 isize }
assign_from! { u32; pow; PowFrom pow_from }
float_ops!{ f32 f64 }

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
