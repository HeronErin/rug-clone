# Arbitrary-precision floating-point numbers

The `rugflo` crate provides arbitrary-precision floating-point numbers
using the [GNU MPFR Library][mpfr home]. It is one of a group of four
crates:

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

[Documentation][rugflo] for this crate is available. It can also be
helpful to refer to the documentation of the [MPFR][mpfr] library.

The crate provides the [`Float`][float] type, which provides an
arbitrary-precision floating-point number with correct rounding.

## Examples

```rust
extern crate rugflo;
use rugflo::Float;

fn main() {
    // Create a floating-point number with 53 bits of precision.
    // (An f64 has 53 bits of precision too.) 
    let flo53 = Float::from((0xff00ff, 53));
    assert!(flo53.to_f64() == 0xff00ff as f64);
    // Create a floating-point number with only 16 bits of precision.
    let flo16 = Float::from((0xff00ff, 16));
    // Now the number is rounded.
    assert!(flo16.to_f64() == 0xff0100 as f64);
}
```

## Usage

To use `rugflo` in your crate, add `extern crate rugflo;` to the crate
root and add `rugflo` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugflo = "0.2.0"
```

The `rugflo` crate depends on the low-level bindings in the
`gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
[documentation][sys] for some details.

### Optional feature

The `rugflo` crate has an optional feature `random` to enable random
number generation. The `random` feature introduces a dependency on the
`rand` crate. The feature is enabled by default; to disable it add
this to `Cargo.toml`:

```toml
[dependencies.rugflo]
version = "0.2.0"
default-features = false
```

[float]:     https://tspiteri.gitlab.io/gmp-mpfr/rugflo/struct.Float.html
[gpl]:       https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:      https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpfr home]: http://www.mpfr.org/
[mpfr]:      https://tspiteri.gitlab.io/gmp-mpfr/mpfr/
[rugcom]:    https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
[rugflo]:    https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
[rugint]:    https://tspiteri.gitlab.io/gmp-mpfr/rugint/
[rugrat]:    https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
[sys]:       https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/
