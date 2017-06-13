# Arbitrary-precision rational numbers

The `rugint` crate provides arbitrary-precision integers using the
[GNU Multiple Precision Arithmetic Library][gmp home] (GMP). It is one
of a group of four crates:

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

[Documentation][rugrat] for this crate is available. It can also be
helpful to refer to the documentation of the [GMP][gmp] library.

The crate provides the [`Rational`][rational] type, which holds an
arbitrary-precision rational number.

## Examples

```rust
extern crate rugrat;
use rugrat::Rational;

fn main() {
    // Create a rational number, -22 / 4 = -11 / 2.
    let rat = Rational::from((-22, 4));
    assert!(rat == (-44, 8));
    assert!(rat.to_f32() == -5.5);
    // The numerator and denominator are stored in canonical form.
    assert!(*rat.numer() == -11);
    assert!(*rat.denom() == 2);
}
```

## Usage

To use `rugint` in your crate, add `extern crate rugrat;` to the crate
root and add `rugrat` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugrat = "0.4.0"
```

The `rugrat` crate depends on the low-level bindings in the
`gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
[documentation][sys] for some details.

[gmp home]: https://gmplib.org/
[gmp]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp/
[gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
[rational]: https://tspiteri.gitlab.io/gmp-mpfr/rugrat/struct.Rational.html
[rugcom]:   https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
[rugflo]:   https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
[rugint]:   https://tspiteri.gitlab.io/gmp-mpfr/rugint/
[rugrat]:   https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
[sys]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/
