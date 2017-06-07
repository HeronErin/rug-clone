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

//! # Arbitrary-precision integers
//!
//! The `rugint` crate provides arbitrary-precision integers using the
//! [GNU Multiple Precision Arithmetic Library][gmp home] (GMP). It is
//! one of a group of four crates:
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
//! documentation of the [GMP][gmp] library.
//!
//! The crate provides the [`Integer`][integer] type, which holds an
//! arbitrary-precision integer. You can construct this from primitive
//! data types, and use the standard arithmetic operators. Many
//! operators can also operate on a mixture of this type and primitive
//! types; in this case, the result is returned as an
//! arbitrary-precision type.
//!
//! ## Examples
//!
//! ```rust
//! extern crate rugint;
//! use rugint::{Assign, Integer};
//!
//! fn main() {
//!     // Create an integer initialized as zero.
//!     let mut int = Integer::new();
//!     assert_eq!(int, 0);
//!     assert_eq!(int.to_u32(), Some(0));
//!     int.assign(14);
//!     assert_eq!(int, 14);
//!     assert_eq!(int.to_i32(), Some(14));
//! }
//! ```
//!
//! Arithmetic operations with mixed arbitrary and primitive types are
//! allowed.
//!
//! ```rust
//! use rugint::Integer;
//! let mut a = Integer::from(0xc);
//! a = (a << 80) + 0xffee;
//! assert_eq!(a.to_string_radix(16), "c0000000000000000ffee");
//! //                                  ^   ^   ^   ^   ^
//! //                                 80  64  48  32  16
//! ```
//!
//! Note that in the above example, there is only one allocation. The
//! `Integer` instance is moved into the shift operation so that the
//! result can be stored in the same instance, then that result is
//! similarly consumed by the addition operation.
//!
//! ## Usage
//!
//! To use `rugint` in your crate, add `extern crate rugint;` to the
//! crate root and add `rugint` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugint = "0.4.0"
//! ```
//!
//! The `rugint` crate depends on the low-level bindings in the
//! `gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
//! macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
//! [documentation][sys] for some details.
//!
//! ### Optional feature
//!
//! The `rugint` crate has an optional feature `random` to enable
//! random number generation. The `random` feature introduces a
//! dependency on the `rand` crate. The feature is enabled by default;
//! to disable it add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rugint]
//! version = "0.4.0"
//! default-features = false
//! ```
//!
//! [gmp home]: https://gmplib.org/
//! [gmp]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp/
//! [gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
//! [integer]:  struct.Integer.html
//! [lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
//! [rugcom]:   https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
//! [rugflo]:   https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
//! [rugint]:   https://tspiteri.gitlab.io/gmp-mpfr/rugint/
//! [rugrat]:   https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
//! [sys]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/

#![warn(missing_docs)]
#![doc(test(attr(deny(warnings))))]

extern crate gmp_mpfr_sys;
#[cfg(feature = "random")]
extern crate rand;

mod integer;
mod small_integer;
mod xgmp;

pub use integer::{Integer, IsPrime, ParseIntegerError};
pub use small_integer::SmallInteger;

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
/// use rugint::{Integer, SubFromAssign};
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
/// use rugint::{DivFromAssign, Integer};
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
/// use rugint::{Integer, RemFromAssign};
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
