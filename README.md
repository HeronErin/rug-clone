# Arbitrary-precision rational numbers

The `rugrat` crate provides arbitrary-precision rational numbers using
the [GNU Multiple Precision Arithmetic Library](https://gmplib.org/)
(GMP). It is one of a group of four crates:

  * [`rugint`](https://tspiteri.gitlab.io/gmp-mpfr/rugint/)
    for arbitrary-precision integers,
  * [`rugrat`](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/)
    for arbitrary-precision rational numbers,
  * [`rugflo`](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/)
    for multiple-precision floating-point numbers, and
  * [`rugcom`](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/)
    for multiple-precision complex numbers.

## Documentation

[Documentation](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/) for this
crate is available.

It can also be helpful to refer to the documentation at the
[GMP](https://gmplib.org/manual/) page.

The crate provides the
[`Rational`](http://tspiteri.gitlab.io/gmp-mpfr/current/rugrat/struct.Rational.html)
type, which holds an arbitrary-precision rational number.

## Examples

```rust
extern crate rugint;
extern crate rugrat;
use rugint::Assign;
use rugrat::Rational;

fn main() {
    // Create a rational number, -22 / 4 = -11 / 2.
    let rat = Rational::from((-22, 4));
    assert!(rat.numer().to_i32() == -11);
    assert!(*rat.denom() == 2);
    assert!(rat.to_f32() == -5.5);
}
```

## Usage

To use this crate, add `rugrat` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugrat = "0.1"
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
