# Multiple-precision complex numbers

The `rugcom` crate provides multiple-precision complex numbers using
[GNU MPC](http://www.multiprecision.org/), a library for the
arithmetic of complex numbers with arbitrarily high precision and
correct rounding of the result. It is one of a group of four crates:

* [`rugint`](https://gitlab.com/tspiteri/rugint)
  provides arbitrary-precision integers based on GMP.
* [`rugrat`](https://gitlab.com/tspiteri/rugrat)
  provides arbitrary-precision rational number based on GMP.
* [`rugflo`](https://gitlab.com/tspiteri/rugflo)
  provides arbitrary-precision floating-point numbers based on MPFR.
* [`rugcom`](https://gitlab.com/tspiteri/rugcom)
  provides arbitrary-precision complex numbers based on MPC.

This crate is free software: you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
  
See [LICENSE-LGPL](LICENSE-LGPL.md) and [LICENSE-GPL](LICENSE-GPL.md)
for details.

## Documentation

[Documentation](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/) for this crate
is available.

It can also be helpful to refer to the documentation at the
[MPC](http://www.multiprecision.org/index.php?prog=mpc&page=html)
page.

The crate provides the
[`Complex`]
(http://tspiteri.gitlab.io/gmp-mpfr/current/rugcom/struct.Complex.html)
type, which holds a multiple-precision complex number.

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
[`gmp-mpfr-sys`](https://gitlab.com/tspiteri/gmp-mpfr-sys) crate. This
should be transparent on GNU/Linux and macOS, but may need some work
on Windows. See
[`gmp-mpfr-sys`](https://gitlab.com/tspiteri/gmp-mpfr-sys) for some
details.

### Optional feature

The `rugcom` crate has an optional feature `random` to enable random
number generation. The `random` feature has a build dependency on the
`rand` crate. The feature is enabled by default; to disable it add
this to `Cargo.toml`:

```toml
[dependencies.rugcom]
version = "0.2.0"
default-features = false
```
