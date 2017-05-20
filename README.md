# Arbitrary-precision integers

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

[Documentation][rugint] for this crate is available. It can also be
helpful to refer to the documentation of the [GMP][gmp] library.

The crate provides the [`Integer`][integer] type, which holds an
arbitrary-precision integer. You can construct this from primitive
data types, and use the standard arithmetic operators. Many operators
can also operate on a mixture of this type and primitive types; in
this case, the result is returned as an arbitrary-precision type.

## Examples

```rust
extern crate rugint;
use rugint::{Assign, Integer};

fn main() {
    // Create an integer initialized as zero.
    let mut int = Integer::new();
    assert!(int == 0);
    assert!(int.to_u32() == Some(0));
    int.assign(14);
    assert!(int == 14);
    assert!(int.to_i32() == Some(14));
}
```

Arithmetic operations with mixed arbitrary and primitive types are
allowed.

```rust
use rugint::Integer;
let mut a = Integer::from(0xc);
a = (a << 80) + 0xffee;
assert!(a.to_string_radix(16) == "c0000000000000000ffee");
//                                 ^   ^   ^   ^   ^
//                                80  64  48  32  16
```

Note that in the above example, there is only one allocation. The
`Integer` instance is moved into the shift operation so that the
result can be stored in the same instance, then that result is
similarly consumed by the addition operation.

## Usage

To use `rugint` in your crate, add `extern crate rugint;` to the crate
root and add `rugint` as a dependency in `Cargo.toml`:

```toml
[dependencies]
rugint = "0.2.2"
```

The `rugint` crate depends on the low-level bindings in the
`gmp-mpfr-sys` crate. This should be transparent on GNU/Linux and
macOS, but may need some work on Windows. See the `gmp-mpfr-sys`
[documentation][sys] for some details.

### Optional feature

The `rugint` crate has an optional feature `random` to enable random
number generation. The `random` feature introduces a dependency on the
`rand` crate. The feature is enabled by default; to disable it add
this to `Cargo.toml`:

```toml
[dependencies.rugint]
version = "0.2.2"
default-features = false
```

[gmp home]: https://gmplib.org/
[gmp]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp/
[gpl]:      https://www.gnu.org/licenses/gpl-3.0.html
[integer]:  https://tspiteri.gitlab.io/gmp-mpfr/rugint/struct.Integer.html
[lgpl]:     https://www.gnu.org/licenses/lgpl-3.0.en.html
[rugcom]:   https://tspiteri.gitlab.io/gmp-mpfr/rugcom/
[rugflo]:   https://tspiteri.gitlab.io/gmp-mpfr/rugflo/
[rugint]:   https://tspiteri.gitlab.io/gmp-mpfr/rugint/
[rugrat]:   https://tspiteri.gitlab.io/gmp-mpfr/rugrat/
[sys]:      https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/
