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
//! using the [GNU Multiple Precision Arithmetic
//! Library](https://gmplib.org/) (GMP). It can be helpful to refer to
//! the documentation at the [GMP](https://gmplib.org/manual/) page.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version.
//!
//! See [LICENSE-LGPL](https://www.gnu.org/licenses/lgpl-3.0.en.html)
//! and [LICENSE-GPL](https://www.gnu.org/licenses/gpl-3.0.html) for
//! details.
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
//! The crate provides the [`Rational`](./struct.Rational.html) type,
//! which holds an arbitrary-precision rational number.
//!
//! ## Examples
//!
//! ```rust
//! use rugrat::Rational;
//! // Create a rational number, -22 / 4 = -11 / 2.
//! let rat = Rational::from((-22, 4));
//! assert!(rat.numer().to_i32() == -11);
//! assert!(*rat.denom() == 2);
//! assert!(rat.to_f32() == -5.5);
//! ```
//!
//! ## Usage
//!
//! To use `rugrat` in your crate, add `extern crate rugrat;` to the
//! crate root and add `rugrat` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugrat = "0.1.3"
//! ```
//!
//! The `rugrat` crate depends on the low-level bindings in the
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! crate. This should be transparent on GNU/Linux and macOS, but may
//! need some work on Windows. See
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! for some details.

extern crate gmp_mpfr_sys;
extern crate rugint;

mod rational;

pub use rational::{MutNumerDenom, Rational};
