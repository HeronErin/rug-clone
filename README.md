# Multiple-precision floating-point numbers

The `rugflo` crate provides multiple-precision floating-point numbers
using the [GNU MPFR Library](http://www.mpfr.org/), a library for
multiple-precision floating-point computations. It is one of a group
of four crates:

  * [`rugint`](https://tspiteri.gitlab.io/gmp-mpfr/rugint/)
    for arbitrary-precision integers,
  * [`rugrat`](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/)
    for arbitrary-precision rational numbers,
  * [`rugflo`](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/)
    for multiple-precision floating-point numbers, and
  * [`rugcom`](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/)
    for multiple-precision complex numbers.

## Documentation

[Documentation](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/) for this
crate is available.

It can also be helpful to refer to the documentation at the
[MPFR](http://www.mpfr.org/mpfr-current/mpfr.html) page.

The crate provides the
[`Float`](http://tspiteri.gitlab.io/gmp-mpfr/current/rugflo/struct.Float.html)
type, which holds a multiple-precision floating-point number.

## Examples

```rust
extern crate rugint;
extern crate rugflo;
use rugint::Assign;
use rugflo::Float;

fn main() {
    // Create a floating-point number with 53 bits of precision.
    // (An `f64` has 53 bits of precision too.) 
    let flo53 = Float::from((0xff00ff, 53));
    assert!(flo.to_f64() == 0xff00ff as f64);
    // Create a floating-point number with only 16 bits of precision.
    let flo16 = Float::from((0xff00ff, 16));
    // Now the number is rounded.
    assert!(flo16.to_f64() == 0xff0100 as f64);
}
```

## Usage

To use this crate, add `rugflo` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugflo = "0.1"
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
