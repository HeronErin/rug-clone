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

//! # Arbitrary-precision numbers
//!
//! The `rug` crate provides integers and floating-point numbers with
//! arbitrary precision and correct rounding. Its main features are:
//!
//! * big [integers][rug int] with arbitrary precision,
//! * big [rational numbers][rug rat] with arbitrary precision,
//! * multi-precision [floating-point numbers][rug flo] with correct
//!   rounding, and
//! * multi-precision [complex numbers][rug com] with correct
//!   rounding.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version. See the full text
//! of the [GNU LGPL][lgpl] and [GNU GPL][gpl] for details.
//!
//! ## Basic use
//!
//! This crate depends on the low-level bindings in the
//! [`gmp-mpfr-sys`][sys] crate, which provides Rust FFI bindings for:
//!
//! * the [GNU Multiple Precision Arithmetic Library][gmp] (GMP),
//! * the [GNU MPFR Library][mpfr], a library for multiple-precision
//!   floating-point computations, and
//! * [GNU MPC][mpc], a library for the arithmetic of complex numbers
//!   with arbitrarily high precision.
//!
//! It can be helpful to refer to the documentation of the
//! [GMP][gmp doc], [MPFR][mpfr doc] and [MPC][mpc doc] libraries.
//!
//! ## Examples
//!
//! ```rust
//! extern crate rug;
//! # #[cfg(feature = "integer")]
//! use rug::{Assign, Integer};
//!
//! fn main() {
//! # #[cfg(feature = "integer")] {
//!     // Create an integer initialized as zero.
//!     let mut int = Integer::new();
//!     assert_eq!(int, 0);
//!     int.assign(14);
//!     assert_eq!(int, 14);
//!     let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
//!     int.assign_str_radix(hex_160, 16).unwrap();
//!     assert_eq!(int.significant_bits(), 160);
//!     int = (int >> 128) - 1;
//!     assert_eq!(int, 0xfffe_ffff_u32);
//! # }
//! }
//! ```
//!
//! ## Usage
//!
//! To use `rug` in your crate, add `extern crate rug;` to the crate
//! root and add `rug` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rug = "0.8.0"
//! ```
//!
//! The `rug` crate depends on the low-level bindings in the
//! [`gmp-mpfr-sys`][sys] crate. This should be transparent on
//! GNU/Linux and macOS, but may need some work on Windows. See the
//! [`gmp-mpfr-sys`][sys] documentation for some details.
//!
//! ### Optional features
//!
//! The `rug` crate has six optional features:
//!
//! 1. `integer`, enabled by default.
//! 2. `rational`, enabled by default. This features depends on the
//!    `integer` feature.
//! 3. `float`, enabled by default.
//! 4. `complex`, enabled by default. This feature depends on the
//!    `float` feature.
//! 5. `rand`, enabled by default.
//! 6. `serde`, disabled by default. This provides serialization
//!    support for the `Integer`, `Rational`, `Float` and `Complex`
//!    types, providing that they are enabled.
//!
//! The first five optional features are enabled by default; to
//! disable them add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rug]
//! version = "0.8.0"
//! default-features = false
//! ```
//!
//! If none of the first five optional features are selected, the
//! [`gmp-mpfr-sys`][sys] crate is not required and thus not enabled.
//!
//! To use features selectively, you can add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rug]
//! version = "0.8.0"
//! default-features = false
//! # Pick which features to use
//! features = ["integer", "float", "rand"]
//! ```
//!
//! Note that both the `rational` feature and the `rand` feature
//! depend on, and will enable, the `integer` feature. Similarly the
//! `complex` feature depends on, and will enable, the `float`
//! feature.
//!
//! [gmp doc]:  https://tspiteri.gitlab.io/gmp-mpfr-sys/gmp/index.html
//! [gmp]:      https://gmplib.org/
//! [gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
//! [lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
//! [mpc doc]:  https://tspiteri.gitlab.io/gmp-mpfr-sys/mpc/index.html
//! [mpc]:      http://www.multiprecision.org/
//! [mpfr doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpfr/index.html
//! [mpfr]:     http://www.mpfr.org/
//! [rug com]:  struct.Complex.html
//! [rug flo]:  struct.Float.html
//! [rug int]:  struct.Integer.html
//! [rug ops]:  ops/index.html
//! [rug rat]:  struct.Rational.html
//! [sys]:      https://docs.rs/gmp-mpfr-sys/^1.0.6/
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/rug/0.8.0/")]
#![doc(test(attr(deny(warnings))))]

#[cfg(any(feature = "integer", feature = "float"))]
extern crate gmp_mpfr_sys;

#[cfg(feature = "serde")]
extern crate serde;
#[cfg(all(test, feature = "serde"))]
extern crate serde_test;

#[macro_use]
mod macros;
mod ext;
mod inner;
#[cfg(feature = "serde")]
mod serdeize;

/// Assigns to a number from another value.
///
/// # Examples
///
/// ```rust
/// use rug::Assign;
/// struct I(i32);
/// impl Assign<i16> for I {
///     fn assign(&mut self, rhs: i16) {
///         self.0 = rhs as i32;
///     }
/// }
/// let mut i = I(0);
/// i.assign(42_i16);
/// assert_eq!(i.0, 42);
/// ```
pub trait Assign<Rhs = Self> {
    /// Peforms the assignement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(15);
    /// assert_eq!(i, 15);
    /// i.assign(23);
    /// assert_eq!(i, 23);
    /// # }
    /// ```
    fn assign(&mut self, rhs: Rhs);
}

pub mod ops;
mod ops_prim;

#[cfg(feature = "integer")]
mod big_integer;
#[cfg(feature = "integer")]
pub use big_integer::Integer;
#[cfg(feature = "integer")]
pub mod integer;

#[cfg(feature = "rational")]
mod big_rational;
#[cfg(feature = "rational")]
pub use big_rational::Rational;
#[cfg(feature = "rational")]
pub mod rational;

#[cfg(feature = "float")]
mod big_float;
#[cfg(feature = "float")]
pub use big_float::Float;
#[cfg(feature = "float")]
pub mod float;

#[cfg(feature = "complex")]
mod big_complex;
#[cfg(feature = "complex")]
pub use big_complex::Complex;
#[cfg(feature = "complex")]
pub mod complex;

#[cfg(feature = "rand")]
pub mod rand;
