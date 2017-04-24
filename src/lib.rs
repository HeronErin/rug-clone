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

//! # Arbitrary-precision floating-point numbers
//!
//! The `rugflo` crate provides arbitrary-precision floating-point
//! numbers using the [GNU MPFR Library][mpfr home], a library for
//! multiple-precision floating-point computations. It is one of a
//! group of four crates:
//!
//! * [`rugint`][rugint] provides arbitrary-precision integers based
//!   on GMP.
//! * [`rugrat`][rugrat] provides arbitrary-precision rational number
//!   based on GMP.
//! * [`rugflo`][rugflo] provides arbitrary-precision floating-point
//!   numbers based on MPFR.
//! * [`rugcom`][rugcom] provides arbitrary-precision complex numbers
//!   based on MPC.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version. See the full text
//! of the [GNU LGPL][lgpl] and [GNU GPL][gpl] for details.
//!
//! ## Basic use
//!
//! Apart from this documentation, it can be helpful to refer to the
//! documentation of the [MPFR][mpfr] library.
//!
//! The crate provides the [`Float`][float] type, which provides an
//! arbitrary-precision floating-point number with correct rounding.
//!
//! ## Examples
//!
//! ```rust
//! extern crate rugflo;
//! use rugflo::Float;
//!
//! fn main() {
//!     // Create a floating-point number with 53 bits of precision.
//!     // (An f64 has 53 bits of precision too.)
//!     let flo53 = Float::from((0xff00ff, 53));
//!     assert!(flo53.to_f64() == 0xff00ff as f64);
//!     // Create a floating-point number with only 16 bits of precision.
//!     let flo16 = Float::from((0xff00ff, 16));
//!     // Now the number is rounded.
//!     assert!(flo16.to_f64() == 0xff0100 as f64);
//! }
//! ```
//!
//! ## Usage
//!
//! To use `rugflo` in your crate, add `extern crate rugflo;` to the
//! crate root and add `rugflo` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugflo = "0.2.1"
//! ```
//!
//! The `rugflo` crate depends on the low-level bindings in the
//! `gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
//! macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
//! [documentation][sys] for some details.
//!
//! ### Optional feature
//!
//! The `rugflo` crate has an optional feature `random` to enable
//! random number generation. The `random` feature introduces a
//! dependency on the `rand` crate. The feature is enabled by default;
//! to disable it add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rugflo]
//! version = "0.2.1"
//! default-features = false
//! ```
//!
//! [float]:     https://tspiteri.gitlab.io/gmp-mpfr/rugflo/struct.Float.html
//! [gpl]:       https://www.gnu.org/licenses/gpl-3.0.html
//! [lgpl]:      https://www.gnu.org/licenses/lgpl-3.0.en.html
//! [mpfr home]: http://www.mpfr.org/
//! [mpfr]:      https://tspiteri.gitlab.io/gmp-mpfr/mpfr/
//! [rugcom]:    https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
//! [rugflo]:    https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
//! [rugint]:    https://tspiteri.gitlab.io/gmp-mpfr/rugint/
//! [rugrat]:    https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
//! [sys]:       https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/

#![warn(missing_docs)]
#![doc(test(attr(deny(warnings))))]

extern crate gmp_mpfr_sys;
#[cfg(feature = "random")]
extern crate rand;
extern crate rugint;
extern crate rugrat;

mod float;

pub use float::{Constant, Float, ParseFloatError, Round, Special, exp_max,
                exp_min, prec_max, prec_min};

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
    where Self: Sized
{
    /// The rounding method.
    type Round;
    /// The direction from rounding.
    type Ordering;
    /// Performs the conversion.
    fn from_round(val: Val,
                  prec: Prec,
                  round: Self::Round)
                  -> (Self, Self::Ordering);
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
    fn add_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn sub_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn mul_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn div_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn shl_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn shr_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
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
    fn pow_round(self,
                 rhs: Rhs,
                 round: Self::Round)
                 -> (Self::Output, Self::Ordering);
}
