// Copyright © 2016–2021 University of Malta

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License and
// a copy of the GNU General Public License along with this program. If not, see
// <https://www.gnu.org/licenses/>.

/*!
Arbitrary-precision rational numbers.

This module provides support for arbitrary-precision rational numbers of type
[`Rational`][crate::Rational].
*/

mod arith;
pub(crate) mod big;
mod casts;
mod cmp;
#[cfg(feature = "serde")]
mod serde;
mod small;
#[cfg(test)]
mod tests;
mod traits;

pub use crate::rational::big::ParseRationalError;
pub use crate::rational::small::SmallRational;

/**
An error which can be returned when a checked conversion from a floating-point
number to a [`Rational`][crate::Rational] number fails.

# Examples

```rust
use core::convert::TryFrom;
use rug::{rational::TryFromFloatError, Rational};
// This is not finite and cannot be converted to Rational.
let inf = 1.0f32 / 0.0;
let error: TryFromFloatError = match Rational::try_from(inf) {
    Ok(_) => unreachable!(),
    Err(error) => error,
};
println!("Error: {}", error);
```
*/
#[derive(Clone, Copy, Debug)]
pub struct TryFromFloatError {
    pub(crate) _unused: (),
}
