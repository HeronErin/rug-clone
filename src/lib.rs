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
//! [GNU Multiple Precision Arithmetic Library](https://gmplib.org/)
//! (GMP). It can be helpful to refer to the documentation at the
//! [GMP](https://gmplib.org/manual/) page.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version.
//!
//! See the [LGPL](https://www.gnu.org/licenses/lgpl-3.0.en.html) and
//! [GPL](https://www.gnu.org/licenses/gpl-3.0.html) for details.
//!
//! This crate is one of a group of four crates:
//!
//! * [`rugint`](https://tspiteri.gitlab.io/gmp-mpfr/rugint/)
//!   provides arbitrary-precision integers based on GMP.
//! * [`rugrat`](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/)
//!   provides arbitrary-precision rational number based on GMP.
//! * [`rugflo`](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/)
//!   provides arbitrary-precision floating-point numbers based on MPFR.
//! * [`rugcom`](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/)
//!   provides arbitrary-precision complex numbers based on MPC.
//!
//! ## Basic use
//!
//! The crate provides the [`Integer`](./struct.Integer.html) type,
//! which holds an arbitrary-precision integer. You can construct this
//! from primitive data types, and use the standard arithmetic
//! operators. Many operators can also operate on a mixture of this
//! type and primitive types; in this case, the result is returned as
//! an arbitrary-precision type.
//!
//! ## Examples
//!
//! ```rust
//! use rugint::{Assign, Integer};
//! // Create an integer initialized as zero.
//! let mut int = Integer::new();
//! assert!(int == 0);
//! assert!(int.to_u32() == Some(0));
//! int.assign(14);
//! assert!(int == 14);
//! assert!(int.to_i32() == Some(14));
//! ```
//!
//! Arithmetic operations with mixed arbitrary and primitive types are
//! allowed. However, the supported operations are not exhaustive.
//!
//! ```rust
//! use rugint::Integer;
//! let mut a = Integer::from(0xc);
//! a = (a << 80) + 0xffee;
//! println!("{}", a.to_string_radix(16));
//! assert!(a.to_string_radix(16) == "c0000000000000000ffee");
//! //                                 ^   ^   ^   ^   ^
//! //                                80  64  48  32  16
//! ```
//!
//! Note that in the above example, there is only one construction.
//! The `Integer` instance is moved into the shift operation so that
//! the result can be stored in the same instance, then that result is
//! similarly consumed by the addition operation.
//!
//! ## Usage
//!
//! To use `rugint` in your crate, add `extern crate rugint;` to the
//! crate root and add `rugint` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugint = "0.1.3"
//! ```
//!
//! The `rugint` crate depends on the low-level bindings in the
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! crate. This should be transparent on GNU/Linux and macOS, but may
//! need some work on Windows. See
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! for some details.
//!
//! ### Optional feature
//!
//! The `rugint` crate has an optional feature `random` to enable
//! random number generation. The `random` feature has a build
//! dependency on the `rand` crate. The feature is enabled by default;
//! to disable it add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rugint]
//! version = "0.1.3"
//! default-features = false
//! ```

extern crate gmp_mpfr_sys;
#[cfg(feature = "random")]
extern crate rand;

mod integer;

pub use integer::{Integer, ParseIntegerError};

/// Assigns to a number from another value.
pub trait Assign<T> {
    /// Peforms the assignement.
    fn assign(&mut self, T);
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
/// assert!(rhs == 90);
/// ```
pub trait SubFromAssign<Lhs = Self> {
    /// Peforms the subtraction.
    fn sub_from_assign(&mut self, Lhs);
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
/// assert!(rhs == 10);
/// ```
pub trait DivFromAssign<Lhs = Self> {
    /// Peforms the division.
    fn div_from_assign(&mut self, Lhs);
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
/// assert!(rhs == 1);
/// ```
pub trait RemFromAssign<Lhs = Self> {
    /// Peforms the remainder operation.
    fn rem_from_assign(&mut self, Lhs);
}

/// Provides the power operation.
pub trait Pow<T> {
    /// The resulting type after the power operation.
    type Output;
    /// Performs the power operation.
    fn pow(self, T) -> Self::Output;
}

/// Provides the power operation inside `self`.
pub trait PowAssign<T> {
    /// Peforms the power operation.
    fn pow_assign(&mut self, T);
}
