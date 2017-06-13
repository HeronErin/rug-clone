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

//! Crate `rug`.

#![warn(missing_docs)]
#![doc(test(attr(deny(warnings))))]

extern crate gmp_mpfr_sys;
#[cfg(feature = "rand")]
extern crate rand;

mod integer;
mod rational;
mod float;
mod complex;

pub use integer::*;
pub use rational::*;
pub use float::*;
pub use complex::*;

/// Assigns to a number from another value.
pub trait Assign<Rhs = Self> {
    /// Peforms the assignement.
    fn assign(&mut self, rhs: Rhs);
}

/// Negates the value inside `self`.
pub trait NegAssign {
    /// Peforms the negation.
    fn neg_assign(&mut self);
}

/// Peforms a bitwise complement of the value inside `self`.
pub trait NotAssign {
    /// Peforms the complement.
    fn not_assign(&mut self);
}

/// Subtract and assigns the result to the rhs operand.
///
/// `rhs.sub_from_assign(lhs)` has the same effect as
/// `rhs = lhs - rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::{Integer, SubFromAssign};
/// let mut rhs = Integer::from(10);
/// rhs.sub_from_assign(100);
/// // rhs = 100 - 10
/// assert_eq!(rhs, 90);
/// ```
pub trait SubFromAssign<Lhs = Self> {
    /// Peforms the subtraction.
    fn sub_from_assign(&mut self, lhs: Lhs);
}

/// Divide and assign the result to the rhs operand.
///
/// `rhs.div_from_assign(lhs)` has the same effect as
/// `rhs = lhs / rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::{DivFromAssign, Integer};
/// let lhs = Integer::from(50);
/// let mut rhs = Integer::from(5);
/// rhs.div_from_assign(lhs);
/// // rhs = 50 / 5
/// assert_eq!(rhs, 10);
/// ```
pub trait DivFromAssign<Lhs = Self> {
    /// Peforms the division.
    fn div_from_assign(&mut self, lhs: Lhs);
}

/// Compute the remainder and assign the result to the rhs operand.
///
/// `rhs.rem_from_assign(lhs)` has the same effect as
/// `rhs = lhs % rhs`.
///
/// # Examples
///
/// ```rust
/// use rug::{Integer, RemFromAssign};
/// let lhs = Integer::from(17);
/// let mut rhs = Integer::from(2);
/// rhs.rem_from_assign(&lhs);
/// // rhs = 17 / 2
/// assert_eq!(rhs, 1);
/// ```
pub trait RemFromAssign<Lhs = Self> {
    /// Peforms the remainder operation.
    fn rem_from_assign(&mut self, lhs: Lhs);
}

/// Provides the power operation.
pub trait Pow<Rhs> {
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    fn pow(self, rhs: Rhs) -> Self::Output;
}

/// Provides the power operation inside `self`.
pub trait PowAssign<Rhs> {
    /// Peforms the power operation.
    fn pow_assign(&mut self, rhs: Rhs);
}

/// Calculate the power and assign the result to the rhs operand.
///
/// `rhs.pow_from_assign(lhs)` has the same effect as
/// `rhs = lhs.pow(rhs)`.
pub trait PowFromAssign<Lhs = Self> {
    /// Peforms the power operation.
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
    fn assign_round(&mut self, rhs: Rhs, round: Self::Round) -> Self::Ordering;
}

/// Construct `Self` via a conversion with a specified precision,
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
    fn from_round(
        val: Val,
        prec: Prec,
        round: Self::Round,
    ) -> (Self, Self::Ordering);
}

/// Provides addition with a specified rounding method.
pub trait AddRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the addition.
    type Output;
    /// Performs the addition.
    fn add_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides subtraction with a specified rounding method.
pub trait SubRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the subtraction.
    type Output;
    /// Performs the subtraction.
    fn sub_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides multiplication with a specified rounding method.
pub trait MulRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the multiplication.
    type Output;
    /// Performs the multiplication.
    fn mul_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides division with a specified rounding method.
pub trait DivRound<Rhs = Self> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the division.
    type Output;
    /// Performs the division.
    fn div_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides the left shift operation with a specified rounding
/// method.
pub trait ShlRound<Rhs> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the left shift operation.
    type Output;
    /// Performs the left shift operation.
    fn shl_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides the right shift operation with a specified rounding
/// method.
pub trait ShrRound<Rhs> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the right shift operation.
    type Output;
    /// Performs the right shift operation.
    fn shr_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}

/// Provides the power operation inside `self` with a specified
/// rounding method.
pub trait PowRound<Rhs> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    fn pow_round(
        self,
        rhs: Rhs,
        round: Self::Round,
    ) -> (Self::Output, Self::Ordering);
}
