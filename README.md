# Arbitrary-precision integers

The `rugint` crate provides arbitrary-precision integers using the
[GNU Multiple Precision Arithmetic Library](https://gmplib.org/)
(GMP). It is one of a group of four crates:

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

[Documentation](https://tspiteri.gitlab.io/gmp-mpfr/rugint/) for this
crate is available.

It can also be helpful to refer to the documentation at the
[GMP](https://gmplib.org/manual/) page.

The crate provides the
[`Integer`]
(http://tspiteri.gitlab.io/gmp-mpfr/current/rugint/struct.Integer.html)
type, which holds an arbitrary-precision integer. You can construct
this from primitive data types, and use the standard arithmetic
operators. Many operators can also operate on a mixture of this type
and primitive types; in this case, the result is returned as an
arbitrary-precision type.

## Examples

```rust
extern crate rugint;
use rugint::{Assign, Integer};

fn main() {
    // Create an integer initialized as zero.
    let mut int = Integer::new();
    assert!(int.to_u32() == 0);
    assert!(int == 0);
    int.assign(14);
    assert!(int == 14);
}
```

Arithmetic operations with mixed arbitrary and primitive types are
allowed. However, the supported operations are not exhaustive.

```rust
use rugint::Integer;
let mut a = Integer::from(0xc);
a = (a << 80) + 0xffee;
assert!(a.to_string_radix(16) == "c0000000000000000ffee");
//                                 ^   ^   ^   ^   ^
//                                80  64  48  32  16
```

Note that in the above example, there is only one construction.
The `Integer` instance is moved into the shift operation so that
the result can be stored in the same instance, then that result is
similarly consumed by the addition operation.

## Usage

To use `rugint` in your crate, add `extern crate rugint;` to the crate
root and add `rugint` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugint = "0.1.3"
```

The `rugint` crate depends on the low-level bindings in the
[`gmp-mpfr-sys`](https://gitlab.com/tspiteri/gmp-mpfr-sys) crate. This
should be transparent on GNU/Linux and macOS, but may need some work
on Windows. See
[`gmp-mpfr-sys`](https://gitlab.com/tspiteri/gmp-mpfr-sys) for some
details.

### Optional feature

The `rugint` crate has an optional feature `random` to enable random
number generation. The `random` feature has a build dependency on the
`rand` crate. The feature is enabled by default; to disable it add
this to `Cargo.toml`:

```toml
[dependencies.rugint]
version = "0.1.3"
default-features = false
```
