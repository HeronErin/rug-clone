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

/// Assigns to a number from another value.
pub trait Assign<Rhs = Self> {
    /// Peforms the assignement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(15);
    /// assert_eq!(i, 15);
    /// i.assign(23);
    /// assert_eq!(i, 23);
    /// ```
    fn assign(&mut self, rhs: Rhs);
}

/// Compound negation and assignment.
pub trait NegAssign {
    /// Peforms the negation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::NegAssign;
    /// let mut i = Integer::from(-42);
    /// i.neg_assign();
    /// assert_eq!(i, 42);
    /// ```
    fn neg_assign(&mut self);
}

/// Compound bitwise complement and assignement.
pub trait NotAssign {
    /// Peforms the complement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::NotAssign;
    /// let mut i = Integer::from(-42);
    /// i.not_assign();
    /// assert_eq!(i, !-42);
    /// ```
    fn not_assign(&mut self);
}

/// Subtract and assigns the result to the rhs operand.
///
/// `rhs.sub_from_assign(lhs)` has the same effect as
/// `rhs = lhs - rhs`.
pub trait SubFromAssign<Lhs = Self> {
    /// Peforms the subtraction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::SubFromAssign;
    /// let mut rhs = Integer::from(10);
    /// rhs.sub_from_assign(100);
    /// // rhs = 100 - 10
    /// assert_eq!(rhs, 90);
    /// ```
    fn sub_from_assign(&mut self, lhs: Lhs);
}

/// Divide and assign the result to the rhs operand.
///
/// `rhs.div_from_assign(lhs)` has the same effect as
/// `rhs = lhs / rhs`.
pub trait DivFromAssign<Lhs = Self> {
    /// Peforms the division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::DivFromAssign;
    /// let lhs = Integer::from(50);
    /// let mut rhs = Integer::from(5);
    /// rhs.div_from_assign(lhs);
    /// // rhs = 50 / 5
    /// assert_eq!(rhs, 10);
    /// ```
    fn div_from_assign(&mut self, lhs: Lhs);
}

/// Compute the remainder and assign the result to the rhs operand.
///
/// `rhs.rem_from_assign(lhs)` has the same effect as
/// `rhs = lhs % rhs`.
pub trait RemFromAssign<Lhs = Self> {
    /// Peforms the remainder operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::RemFromAssign;
    /// let lhs = Integer::from(17);
    /// let mut rhs = Integer::from(2);
    /// rhs.rem_from_assign(&lhs);
    /// // rhs = 17 / 2
    /// assert_eq!(rhs, 1);
    /// ```
    fn rem_from_assign(&mut self, lhs: Lhs);
}

/// The power operation.
pub trait Pow<Rhs> {
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::Pow;
    /// let base = Integer::from(10);
    /// let ans = base.pow(5);
    /// assert_eq!(ans, 100_000);
    /// ```
    fn pow(self, rhs: Rhs) -> Self::Output;
}

/// Compound power operation and assignment.
pub trait PowAssign<Rhs> {
    /// Peforms the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Integer;
    /// use rug::ops::PowAssign;
    /// let mut i = Integer::from(10);
    /// i.pow_assign(5);
    /// assert_eq!(i, 100_000);
    /// ```
    fn pow_assign(&mut self, rhs: Rhs);
}

/// Compute the power and assign the result to the rhs operand.
///
/// `rhs.pow_from_assign(lhs)` has the same effect as
/// `rhs = lhs.pow(rhs)`.
pub trait PowFromAssign<Lhs = Self> {
    /// Peforms the power operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::Float;
    /// use rug::ops::PowFromAssign;
    /// let lhs = 10;
    /// let mut rhs = Float::from((5, 53));
    /// rhs.pow_from_assign(lhs);
    /// // rhs = 10 ** 5
    /// assert_eq!(rhs, 100_000);
    /// # }
    /// ```
    fn pow_from_assign(&mut self, lhs: Lhs);
}

/// Assigns to a number from another value, applying the specified
/// rounding method.
pub trait AssignRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Peforms the assignment and rounding.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::{AssignRound, Float};
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let mut f = Float::new(4);
    /// let dir = f.assign_round(3.3, Round::Nearest);
    /// // 3.3 rounded down to 3.25
    /// assert_eq!(f, 3.25);
    /// assert_eq!(dir, Ordering::Less);
    /// let dir = f.assign_round(3.3, Round::Up);
    /// // 3.3 rounded up to 3.5
    /// assert_eq!(f, 3.5);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn assign_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Constructs an element via a conversion with a specified precision,
/// applying the specified rounding method.
pub trait FromRound<Val, Prec>
where
    Self: Sized,
{
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the conversion.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "float")] {
    /// use rug::{Float, FromRound};
    /// use rug::float::Round;
    /// use std::cmp::Ordering;
    /// // only four significant bits
    /// let (f, dir) = Float::from_round(3.3, 4, Round::Nearest);
    /// // 3.3 rounded down to 3.25
    /// assert_eq!(f, 3.25);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn from_round(
        val: Val,
        prec: Prec,
        round: Self::Round,
    ) -> (Self, Self::Ordering);
}

/// Addition with a specified rounding method.
pub trait AddRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the addition.
    type Output;
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
    /// let minus_three = Float::from((-3, 4));
    /// let (f, dir) = minus_three.add_round(-0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn add_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Subtraction with a specified rounding method.
pub trait SubRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the subtraction.
    type Output;
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
    /// let minus_three = Float::from((-3, 4));
    /// let (f, dir) = minus_three.sub_round(0.3, Round::Nearest);
    /// // -3.3 rounded up to -3.25
    /// assert_eq!(f, -3.25);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn sub_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Multiplication with a specified rounding method.
pub trait MulRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the multiplication.
    type Output;
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
    /// let minus_three = Float::from((-3, 4));
    /// let (f, dir) = minus_three.mul_round(13, Round::Nearest);
    /// // -39 rounded down to -40
    /// assert_eq!(f, -40);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn mul_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Division with a specified rounding method.
pub trait DivRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the division.
    type Output;
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
    /// let minus_three = Float::from((-3, 4));
    /// let (f, dir) = minus_three.div_round(5, Round::Nearest);
    /// // -0.6 rounded down to -0.625
    /// assert_eq!(f, -0.625);
    /// assert_eq!(dir, Ordering::Less);
    /// # }
    /// ```
    fn div_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// The power operation with a specified rounding method.
pub trait PowRound<Rhs> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the power operation.
    type Output;
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
    /// let minus_three = Float::from((-3, 4));
    /// let (f, dir) = minus_three.pow_round(5, Round::Nearest);
    /// // -243 rounded up to -240
    /// assert_eq!(f, -240);
    /// assert_eq!(dir, Ordering::Greater);
    /// # }
    /// ```
    fn pow_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}
