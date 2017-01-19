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
//! The crate provides the [`Rational`](./struct.Rational.html) type,
//! which holds an arbitrary-precision rational number.
//! 
//! ## Examples
//! 
//! ```rust
//! extern crate rugint;
//! extern crate rugrat;
//! use rugint::Assign;
//! use rugrat::Rational;
//! 
//! fn main() {
//!     // Create a rational number, -22 / 4 = -11 / 2.
//!     let rat = Rational::from((-22, 4));
//!     assert!(rat.numer().to_i32() == -11);
//!     assert!(*rat.denom() == 2);
//!     assert!(rat.to_f32() == -5.5);
//! }
//! ```

extern crate gmp_mpfr_sys;
extern crate rugint;

mod rational;

pub use rational::{MutNumerDenom, Rational};
