# Arbitrary-precision complex numbers

The `rugcom` crate provides arbitrary-precision complex numbers using
[GNU MPC][mpc home], a library for the arithmetic of complex numbers
with arbitrarily high precision and correct rounding of the result. It
is one of a group of four crates:

* [`rugint`][rugint] provides arbitrary-precision integers based on
  GMP.
* [`rugrat`][rugrat] provides arbitrary-precision rational number
  based on GMP.
* [`rugflo`][rugflo] provides arbitrary-precision floating-point
  numbers based on MPFR.
* [`rugcom`][rugcom] provides arbitrary-precision complex numbers
  based on MPC.

This crate is free software: you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version. See the full text of the
[GNU LGPL][lgpl] and [GNU GPL][gpl] for details.

## Basic use

[Documentation][rugcom] for this crate is available. It can also be
helpful to refer to the documentation of the [MPC][mpc] library.

The crate provides the [`Complex`][complex] type, which provides an
arbitrary-precision complex number with correct rounding.

## Examples

```rust
extern crate rugint;
extern crate rugcom;
use rugint::Assign;
use rugcom::Complex;

fn main() {
    // Create complex number with 16 bits of precision.
    let mut com = Complex::new((16, 16));
    // Assign the complex value 1.5 + 3.5i
    com.assign((1.5, 3.5));
    assert!(*com.real() == 1.5);
    assert!(*com.imag() == 3.5);
}
```

## Usage

To use `rugcom` in your crate, add `extern crate rugcom;` to the crate
root and add `rugcom` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugcom = "0.2.0"
```

The `rugcom` crate depends on the low-level bindings in the
`gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
[documentation][sys] for some details.

### Optional feature

The `rugcom` crate has an optional feature `random` to enable random
number generation. The `random` feature introduces a dependency on the
`rand` crate. The feature is enabled by default; to disable it add
this to `Cargo.toml`:

```toml
[dependencies.rugcom]
version = "0.2.0"
default-features = false
```

[complex]:  https://tspiteri.gitlab.io/gmp-mpfr/rugcom/struct.Complex.html
[gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpc home]: http://www.multiprecision.org/
[mpc]:      https://tspiteri.gitlab.io/gmp-mpfr/mpc/
[rugcom]:   https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
[rugflo]:   https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
[rugint]:   https://tspiteri.gitlab.io/gmp-mpfr/rugint/
[rugrat]:   https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
[sys]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/
