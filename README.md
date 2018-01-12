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

[Documentation][rug] for this crate is available. This crate requires
rustc version 1.18.0. This crate depends on the low-level bindings in
the [`gmp-mpfr-sys`][sys] crate, which provides Rust FFI bindings for:

* the [GNU Multiple Precision Arithmetic Library][gmp] (GMP),
* the [GNU MPFR Library][mpfr], a library for multiple-precision
  floating-point computations, and
* [GNU MPC][mpc], a library for the arithmetic of complex numbers with
  arbitrarily high precision.

It can be helpful to refer to the documentation of the [GMP][gmp doc],
[MPFR][mpfr doc] and [MPC][mpc doc] libraries.

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
rug = "0.9.2"
```

The `rug` crate depends on the low-level bindings in the
[`gmp-mpfr-sys`][sys] crate. This should be transparent on GNU/Linux
and macOS, but may need some work on Windows. See the
[`gmp-mpfr-sys`][sys] documentation for some details.

### Optional features

The `rug` crate has six optional features:

1. `integer`, enabled by default.
2. `rational`, enabled by default. This feature requires the `integer`
   feature.
3. `float`, enabled by default.
4. `complex`, enabled by default. This feature requires the `float`
   feature.
5. `rand`, enabled by default. This feature requires the `integer`
   feature.
6. `serde`, disabled by default. This provides serialization support
   for the `Integer`, `Rational`, `Float` and `Complex` types,
   providing that they are enabled.

The first five optional features are enabled by default; to disable
them add this to `Cargo.toml`:

```toml
[dependencies.rug]
version = "0.9.2"
default-features = false
```

If none of the first five optional features are selected, the
[`gmp-mpfr-sys`][sys] crate is not required and thus not enabled.

To use features selectively, you can add this to `Cargo.toml`:

```toml
[dependencies.rug]
version = "0.9.2"
default-features = false
# Pick which features to use
features = ["integer", "float", "rand"]
```

[gmp doc]:  https://tspiteri.gitlab.io/gmp-mpfr-sys/gmp/index.html
[gmp]:      https://gmplib.org/
[gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpc doc]:  https://tspiteri.gitlab.io/gmp-mpfr-sys/mpc/index.html
[mpc]:      http://www.multiprecision.org/
[mpfr doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpfr/index.html
[mpfr]:     http://www.mpfr.org/
[rug com]:  https://docs.rs/rug/0.9.2/rug/struct.Complex.html
[rug flo]:  https://docs.rs/rug/0.9.2/rug/struct.Float.html
[rug int]:  https://docs.rs/rug/0.9.2/rug/struct.Integer.html
[rug ops]:  https://docs.rs/rug/0.9.2/rug/ops/index.html
[rug rat]:  https://docs.rs/rug/0.9.2/rug/struct.Rational.html
[rug]:      https://docs.rs/rug/0.9.2/rug/index.html
[sys]:      https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html
