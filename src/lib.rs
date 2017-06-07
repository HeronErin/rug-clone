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

//! # Arbitrary-precision rational numbers
//!
//! The `rugrat` crate provides arbitrary-precision rational numbers
//! using the [GNU Multiple Precision Arithmetic Library][gmp home]
//! (GMP). It is one of a group of four crates:
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
//! The crate provides the [`Rational`][rational] type, which holds an
//! arbitrary-precision rational number.
//!
//! ## Examples
//!
//! ```rust
//! extern crate rugrat;
//! use rugrat::Rational;
//!
//! fn main() {
//!     // Create a rational number, -22 / 4 = -11 / 2.
//!     let rat = Rational::from((-22, 4));
//!     assert_eq!(rat, (-44, 8));
//!     assert_eq!(rat.to_f32(), -5.5);
//!     // The numerator and denominator are stored in canonical form.
//!     assert_eq!(*rat.numer(), -11);
//!     assert_eq!(*rat.denom(), 2);
//! }
//! ```
//!
//! ## Usage
//!
//! To use `rugrat` in your crate, add `extern crate rugrat;` to the
//! crate root and add `rugrat` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugrat = "0.4.0"
//! ```
//!
//! The `rugrat` crate depends on the low-level bindings in the
//! `gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
//! macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
//! [documentation][sys] for some details.
//!
//! [gmp home]: https://gmplib.org/
//! [gmp]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp/
//! [gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
//! [lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
//! [rational]: struct.Rational.html
//! [rugcom]:   https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
//! [rugflo]:   https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
//! [rugint]:   https://tspiteri.gitlab.io/gmp-mpfr/rugint/
//! [rugrat]:   https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
//! [sys]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/

#![warn(missing_docs)]
#![doc(test(attr(deny(warnings))))]

extern crate gmp_mpfr_sys;
extern crate rugint;

mod rational;
mod small_rational;
mod xgmp;

pub use rational::{MutNumerDenom, ParseRationalError, Rational};
pub use small_rational::SmallRational;
