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

//! # Multiple-precision floating-point numbers
//!
//! The `rugflo` crate provides multiple-precision floating-point
//! numbers using the [GNU MPFR Library](http://www.mpfr.org/), a
//! library for multiple-precision floating-point computations. It
//! can be helpful to refer to the documentation at the
//! [MPFR](http://www.mpfr.org/mpfr-current/mpfr.html) page.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version.
//!
//! This crate is one of a group of four crates:
//!
//!   * [`rugint`](../rugint/index.html) for arbitrary-precision
//!     integers,
//!   * [`rugrat`](../rugrat/index.html) for arbitrary-precision
//!     rational numbers,
//!   * [`rugflo`](../rugflo/index.html) for multiple-precision
//!     floating-point numbers, and
//!   * [`rugcom`](../rugcom/index.html) for multiple-precision
//!     complex numbers.
//!
//! # Basic use
//!
//! The crate provides the [`Float`](./struct.Float.html) type, which
//! holds a multiple-precision floating-point number.
//!
//! ## Examples
//!
//! ```rust
//! use rugflo::Float;
//!
//! // Create a floating-point number with 53 bits of precision.
//! // (An `f64` has 53 bits of precision too.)
//! let flo53 = Float::from((0xff00ff, 53));
//! assert!(flo53.to_f64() == 0xff00ff as f64);
//! // Create a floating-point number with only 16 bits of precision.
//! let flo16 = Float::from((0xff00ff, 16));
//! // Now the number is rounded.
//! assert!(flo16.to_f64() == 0xff0100 as f64);
//! ```

extern crate gmp_mpfr_sys;
#[cfg(feature = "rand")]
extern crate rand;
extern crate rugint;
extern crate rugrat;

mod float;

pub use float::{Constant, Float, Round, Special, exp_max, exp_min, prec_max,
                prec_min};

/// Assigns to a number from another value, applying the specified
/// rounding method.
pub trait AssignRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Peforms the assignment and rounding.
    fn assign_round(&mut self, T, Self::Round) -> Self::Ordering;
}

/// Construct `Self` via a conversion with a specified precision,
/// applying the specified rounding method.
pub trait FromRound<T, P>
    where Self: Sized
{
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the conversion.
    fn from_round(T, P, Self::Round) -> (Self, Self::Ordering);
}

/// Provides addition with a specified rounding method.
pub trait AddRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the addition.
    type Output;
    /// Performs the addition.
    fn add_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides subtraction with a specified rounding method.
pub trait SubRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the subtraction.
    type Output;
    /// Performs the subtraction.
    fn sub_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides multiplication with a specified rounding method.
pub trait MulRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the multiplication.
    type Output;
    /// Performs the multiplication.
    fn mul_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides division with a specified rounding method.
pub trait DivRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the division.
    type Output;
    /// Performs the division.
    fn div_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides the left shift operation with a specified rounding
/// method.
pub trait ShlRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the left shift operation.
    type Output;
    /// Performs the left shift operation.
    fn shl_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides the right shift operation with a specified rounding
/// method.
pub trait ShrRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the right shift operation.
    type Output;
    /// Performs the right shift operation.
    fn shr_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}

/// Provides the power operation inside `self` with a specified
/// rounding method.
pub trait PowRound<T> {
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    fn pow_round(self, T, Self::Round) -> (Self::Output, Self::Ordering);
}
