# Multiple-precision complex numbers

The `rugcom` crate provides multiple-precision complex numbers using
[GNU MPC](http://www.multiprecision.org/), a library for the
arithmetic of complex numbers with arbitrarily high precision and
correct rounding of the result. It is one of a group of four crates:

  * [`rugint`](https://tspiteri.gitlab.io/gmp-mpfr/rugint/)
    for arbitrary-precision integers,
  * [`rugrat`](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/)
    for arbitrary-precision rational numbers,
  * [`rugflo`](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/)
    for multiple-precision floating-point numbers, and
  * [`rugcom`](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/)
    for multiple-precision complex numbers.

## Documentation

[Documentation](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/) for this crate
is available.

It can also be helpful to refer to the documentation at the
[MPC](http://www.multiprecision.org/index.php?prog=mpc&page=html)
page.

The crate provides the
[`Complex`](http://tspiteri.gitlab.io/gmp-mpfr/current/rugcom/struct.Complex.html)
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
    com.assign((1.5, 3.5));
    assert!(*com.real() == 1.5);
    assert!(*com.imag() == 3.5);
}
```

## Usage

To use this crate, add `rugcom` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugcom = "0.1"
```

This crate depends on the low-level bindings in the crate
[`gmp-mpfr-sys`](https://gitlab.com/tspiteri/gmp-mpfr-sys). This
should be transparent on GNU/Linux and macOS, but may need some work
on Windows. See the `gmp-mpfr-sys`
[README](https://gitlab.com/tspiteri/gmp-mpfr-sys/blob/master/README.md)
for some details.

## License

This crate is free software: you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
  
See [LICENSE-LGPL](LICENSE-LGPL.md) and [LICENSE-GPL](LICENSE-GPL.md)
for details.
