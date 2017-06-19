# Arbitrary-precision numbers

The `rug` crate provides integers and floating-point numbers with
arbitrary precision and correct rounding. Its main features are:

* big [integers][rug int] with arbitrary precision,
* big [rational numbers][rug rat] with arbitrary precision,
* multi-precision [floating-point numbers][rug flo] with correct
  rounding, and
* multi-precision [complex numbers][rug com] with correct rounding.

This crate is free software: you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version. See the full text of the
[GNU LGPL][lgpl] and [GNU GPL][gpl] for details.

## Basic use

[Documentation][rug] for this crate is available. This crate depends
on the low-level bindings in the [`gmp-mpfr-sys`][sys] crate, which
provides RUST FFI bindings for:

* the [GNU Multiple Precision Arithmetic Library][gmp home] (GMP),
* the [GNU MPFR Library][mpfr home], a library for multiple-precision
  floating-point computations, and
* [GNU MPC][mpc home], a library for the arithmetic of complex numbers
  with arbitrarily high precision.

It can be helpful to refer to the documentation of the [GMP][gmp],
[MPFR][mpfr] and [MPC][mpc] libraries.

## Examples

```rust
extern crate rug;
use rug::{Assign, Integer};

fn main() {
    // Create an integer initialized as zero.
    let mut int = Integer::new();
    assert_eq!(int, 0);
    int.assign(14);
    assert_eq!(int, 14);
    let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
    int.assign_str_radix(hex_160, 16).unwrap();
    assert_eq!(int.significant_bits(), 160);
    int = (int >> 128) - 1;
    assert_eq!(int, 0xfffe_ffff_u32);
}
```

## Usage

To use `rug` in your crate, add `extern crate rug;` to the crate root
and add `rug` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rug = "0.4.0"
```

The `rug` crate depends on the low-level bindings in the
`gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
[documentation][sys] for some details.

### Optional feature

The `rug` crate has three optional features `rational`, `float` and
`complex`. Integers are always included. The optional features are
enabled by default; to disable them add this to `Cargo.toml`:

```toml
[dependencies.rug]
version = "0.4.0"
default-features = false
```

To use features selectively, you can add this to `Cargo.toml`:

```toml
[dependencies.rug]
version = "0.4.0"
default-features = false
# Pick which features to use
features = ["rational", "float"]
```

Note that the the `complex` feature will enable the `float` feature,
on which it depends.

[gmp home]:  https://gmplib.org/
[gmp]:       https://tspiteri.gitlab.io/rug/gmp/index.html
[gpl]:       https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:      https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpc home]:  http://www.multiprecision.org/
[mpc]:       https://tspiteri.gitlab.io/rug/mpc/index.html
[mpfr home]: http://www.mpfr.org/
[mpfr]:      https://tspiteri.gitlab.io/rug/mpfr/index.html
[rug com]:   https://tspiteri.gitlab.io/rug/rug/struct.Complex.html
[rug flo]:   https://tspiteri.gitlab.io/rug/rug/struct.Float.html
[rug int]:   https://tspiteri.gitlab.io/rug/rug/struct.Integer.html
[rug rat]:   https://tspiteri.gitlab.io/rug/rug/struct.Rational.html
[rug]:       https://tspiteri.gitlab.io/rug/rug/index.html
[sys]:       https://tspiteri.gitlab.io/rug/gmp_mpfr_sys/index.html
