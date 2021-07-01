// Copyright © 2016–2021 Trevor Spiteri

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License and
// a copy of the GNU General Public License along with this program. If not, see
// <https://www.gnu.org/licenses/>.

/*!
# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary precision and
correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision,
  * [`Rational`] is a bignum rational number with arbitrary precision,
  * [`Float`] is a multi-precision floating-point number with correct rounding,
    and
  * [`Complex`] is a multi-precision complex number with correct rounding.

Rug is a high-level interface to the following [GNU] libraries:

  * [GMP] for integers and rational numbers,
  * [MPFR] for floating-point numbers, and
  * [MPC] for complex numbers.

Rug is free software: you can redistribute it and/or modify it under the terms
of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version. See the full text of the [GNU LGPL] and [GNU GPL] for details.

You are also free to use the examples in this documentation without any
restrictions; the examples are in the public domain.

## Quick example

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut int = Integer::new();
assert_eq!(int, 0);
int.assign(14);
assert_eq!(int, 14);

let decimal = "98_765_432_109_876_543_210";
int.assign(Integer::parse(decimal).unwrap());
assert!(int > 100_000_000);

let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
int.assign(Integer::parse_radix(hex_160, 16).unwrap());
assert_eq!(int.significant_bits(), 160);
int = (int >> 128) - 1;
assert_eq!(int, 0xfffe_ffff_u32);
# }
```

  * <code>[Integer]::[new][Integer::new]</code> creates a new [`Integer`]
    intialized to zero.
  * To assign values to Rug types, we use the [`Assign`] trait and its method
    [`Assign::assign`]. We do not use the [assignment operator `=`][assignment]
    as that would drop the left-hand-side operand and replace it with a
    right-hand-side operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to fit in a
    primitive type. To assign such a number to the large types, we use strings
    rather than primitives; in the example this is done using
    <code>[Integer]::[parse][Integer::parse]</code> and
    <code>[Integer]::[parse\_radix][Integer::parse_radix]</code>.
  * We can compare Rug types to primitive types or to other Rug types using the
    normal comparison operators, for example `int > 100_000_000`.
  * Most arithmetic operations are supported with Rug types and primitive types
    on either side of the operator, for example `int >> 128`.

## Using with primitive types

With Rust primitive types, arithmetic operators usually operate on two values of
the same type, for example `12i32 + 5i32`. Unlike primitive types, conversion to
and from Rug types can be expensive, so the arithmetic operators are overloaded
to work on many combinations of Rug types and primitives. The following are
provided:

 1. Where they make sense, all arithmetic operators are overloaded to work with
    Rug types and the primitives [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], [`f32`] and [`f64`].
 2. Where they make sense, conversions using the [`From`] trait and assignments
    using the [`Assign`] trait are supported for all the primitives in 1 above
    as well as [`bool`], [`isize`] and [`usize`].
 3. Comparisons between Rug types and all the numeric primitives listed in 1 and
    2 above are supported.
 4. For [`Rational`] numbers, conversions and comparisons are also supported for
    tuples containing two integer primitives: the first is the numerator and the
    second is the denominator which must not be zero. The two primitives do not
    need to be of the same type.
 5. For [`Complex`] numbers, conversions and comparisons are also supported for
    tuples containing two primitives: the first is the real part and the second
    is the imaginary part. The two primitives do not need to be of the same
    type.

## Operators

Operators are overloaded to work on Rug types alone or on a combination of Rug
types and Rust primitives. When at least one operand is an owned value of a Rug
type, the operation will consume that value and return a value of the Rug type.
For example

```rust
# #[cfg(feature = "integer")] {
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
# }
```

Here `a` is consumed by the subtraction, and `b` is an owned [`Integer`].

If on the other hand there are no owned Rug types and there are references
instead, the returned value is not the final value, but an
incomplete-computation value. For example

```rust
# #[cfg(feature = "integer")] {
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
# }
```

Here `a` and `b` are not consumed, and `incomplete` is not the final value. It
still needs to be converted or assigned into an [`Integer`]. This is covered in
more detail in the [*Incomplete-computation values*] section.

### Shifting operations

The left shift `<<` and right shift `>>` operators support shifting by negative
values, for example `a << 5` is equivalent to `a >> -5`.

The shifting operators are also supported for the [`Float`] and [`Complex`]
number types, where they are equivalent to multiplication or division by a power
of two. Only the exponent of the value is affected; the mantissa is unchanged.

### Exponentiation

Exponentiation (raising to a power) does not have a dedicated operator in Rust.
In order to perform exponentiation of Rug types, the [`Pow`][ops::Pow] trait has
to be brought into scope, for example

```rust
# #[cfg(feature = "integer")] {
use rug::{ops::Pow, Integer};
let base = Integer::from(10);
let power = base.pow(5);
assert_eq!(power, 100_000);
# }
```

### Compound assignments to right-hand-side operands

Traits are provided for compound assignment to right-hand-side operands. This
can be useful for non-commutative operations like subtraction. The names of the
traits and their methods are similar to Rust compound assignment traits, with
the suffix “`Assign`” replaced with “`From`”. For example the counterpart to
[`SubAssign`][core::ops::SubAssign] is [`SubFrom`][ops::SubFrom]:

```rust
# #[cfg(feature = "integer")] {
use rug::{ops::SubFrom, Integer};
let mut rhs = Integer::from(10);
// set rhs = 100 − rhs
rhs.sub_from(100);
assert_eq!(rhs, 90);
# }
```

## Incomplete-computation values

There are two main reasons why operations like `&a - &b` do not perform a
complete computation and return a Rug type:

 1. Sometimes we need to assign the result to an object that already exists.
    Since Rug types require memory allocations, this can help reduce the number
    of allocations. (While the allocations might not affect performance
    noticeably for computationally intensive functions, they can have a much
    more significant effect on faster functions like addition.)
 2. For the [`Float`] and [`Complex`] number types, we need to know the
    precision when we create a value, and the operation itself does not convey
    information about what precision is desired for the result.

There are two things that can be done with incomplete-computation values:

 1. Assign them to an existing object without unnecessary allocations. This is
    usually achieved using the [`Assign`] trait or a similar method, for example
    <code>int.[assign][Assign::assign]\(incomplete)</code> and
    <code>float.[assign\_round][ops::AssignRound::assign_round]\(incomplete,
    [Round][float::Round]::[Up][float::Round::Up])</code>.
 2. Convert them to the final value using the [`Complete`] trait, the [`From`]
    trait or a similar method. For example incomplete integers can be completed
    using <code>incomplete.[complete][Complete::complete]\()</code> or
    <code>[Integer]::[from][From::from]\(incomplete)</code>. Incomplete
    floating-point numbers can be completed using
    <code>[Float]::[with_val][Float::with_val]\(53, incomplete)</code> since the
    precision has to be specified.

Let us consider a couple of examples.

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut buffer = Integer::new();
// ... buffer can be used and reused ...
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
buffer.assign(incomplete);
assert_eq!(buffer, -10);
# }
```

Here the assignment from `incomplete` into `buffer` does not require an
allocation unless the result does not fit in the current capacity of `buffer`.
If `&a - &b` returned an [`Integer`] instead, then an allocation would take
place even if it is not necessary.

```rust
# #[cfg(feature = "float")] {
use rug::{float::Constant, Float};
// x has a precision of 10 bits
let x = Float::with_val(10, 180);
// y has a precision of 50 bits
let y = Float::with_val(50, Constant::Pi);
let incomplete = &x / &y;
// z has a precision of 45 bits
let z = Float::with_val(45, incomplete);
assert!(57.295 < z && z < 57.296);
# }
```

The precision to use for the result depends on the requirements of the algorithm
being implemented. Here `z` is created with a precision of 45.

Many operations can return incomplete-computation values, for example

  * unary operators applied to references, for example `-&int`
  * binary operators applied to two references, for example `&int1 + &int2`
  * binary operators applied to a primitive and a reference, for example `&int *
    10`
  * methods that take a reference, for example
    <code>int.[abs\_ref][Integer::abs_ref]\()</code>
  * methods that take two references, for example
    <code>int1.[gcd\_ref][Integer::gcd_ref]\(\&int2)</code>
  * string parsing, for example
    <code>[Integer]::[parse][Integer::parse]\(\"12\")</code>

These operations return objects that can be stored in temporary variables like
`incomplete` in the last few code examples. However, the names of the types are
not public, and consequently, the incomplete-computation values cannot be for
example stored in a struct. If you need to store the value in a struct, complete
it to its final type and value.

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate, add it as
a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.12"
```

Rug requires rustc version 1.37.0 or later.

Rug also depends on the [GMP], [MPFR] and [MPC] libraries through the low-level
FFI bindings in the [gmp-mpfr-sys crate][sys crate], which needs some setup to
build; the [gmp-mpfr-sys documentation][sys] has some details on usage under
[GNU/Linux][sys gnu], [macOS][sys mac] and [Windows][sys win].

## Optional features

The Rug crate has six optional features:

 1. `integer`, enabled by default. Required for the [`Integer`] type and its
    supporting features.
 2. `rational`, enabled by default. Required for the [`Rational`] number type
    and its supporting features. This feature requires the `integer` feature.
 3. `float`, enabled by default. Required for the [`Float`] type and its
    supporting features.
 4. `complex`, enabled by default. Required for the [`Complex`] number type and
    its supporting features. This feature requires the `float` feature.
 5. `rand`, enabled by default. Required for the [`RandState`][rand::RandState]
    type and its supporting features. This feature requires the `integer`
    feature.
 6. `serde`, disabled by default. This provides serialization support for the
    [`Integer`], [`Rational`], [`Float`] and [`Complex`] number types, providing
    that they are enabled. This feature requires the [serde crate].

The first five optional features are enabled by default; to use features
selectively, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.12"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If none of the
features are selected, the [gmp-mpfr-sys crate][sys crate] is not required and
thus not enabled. In that case, only the [`Assign`] trait and the traits that
are in the [`ops`] module are provided by the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: #incomplete-computation-values
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html
*/
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/rug/~1.12")]
#![doc(html_logo_url = "data:image/svg+xml;base64,
PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iVVRGLTgiPz4KPCEtLSBDcmVhdGVkIHdpdGggSW5rc2NhcGUgKGh0dHA6Ly93
d3cuaW5rc2NhcGUub3JnLykgLS0+Cjxzdmcgd2lkdGg9IjEyOCIgaGVpZ2h0PSIxMjgiIHZlcnNpb249IjEuMSIgdmlld0JveD0i
MCAwIDMzLjg2NjY2NiAzMy44NjY2NjgiIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgeG1sbnM6Y2M9Imh0dHA6
Ly9jcmVhdGl2ZWNvbW1vbnMub3JnL25zIyIgeG1sbnM6ZGM9Imh0dHA6Ly9wdXJsLm9yZy9kYy9lbGVtZW50cy8xLjEvIiB4bWxu
czpyZGY9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkvMDIvMjItcmRmLXN5bnRheC1ucyMiPgogPG1ldGFkYXRhPgogIDxyZGY6UkRG
PgogICA8Y2M6V29yayByZGY6YWJvdXQ9IiI+CiAgICA8ZGM6Zm9ybWF0PmltYWdlL3N2Zyt4bWw8L2RjOmZvcm1hdD4KICAgIDxk
Yzp0eXBlIHJkZjpyZXNvdXJjZT0iaHR0cDovL3B1cmwub3JnL2RjL2RjbWl0eXBlL1N0aWxsSW1hZ2UiLz4KICAgIDxkYzp0aXRs
ZS8+CiAgIDwvY2M6V29yaz4KICA8L3JkZjpSREY+CiA8L21ldGFkYXRhPgogPGcgdHJhbnNmb3JtPSJ0cmFuc2xhdGUoMCAtMjYz
LjEzKSI+CiAgPHBhdGggZD0ibTMzLjg2NyAyODAuMDdhMTYuOTMzIDE2LjkzMyAwIDAgMSAtMTYuOTMzIDE2LjkzMyAxNi45MzMg
MTYuOTMzIDAgMCAxIC0xNi45MzMgLTE2LjkzMyAxNi45MzMgMTYuOTMzIDAgMCAxIDE2LjkzMyAtMTYuOTMzIDE2LjkzMyAxNi45
MzMgMCAwIDEgMTYuOTMzIDE2LjkzM3oiIGZpbGw9IiNmZmZmYzAiLz4KICA8ZyBmaWxsPSJub25lIiBzdHJva2U9IiMwMDAiIHN0
cm9rZS13aWR0aD0iLjI2NDU4cHgiPgogICA8ZyBhcmlhLWxhYmVsPSI2Ij4KICAgIDxwYXRoIGQ9Im0xNC40NzEgMjg0LjA3YzIu
MjAxMyAwIDQuMDM1OC0xLjQ2NzYgNC4wMzU4LTMuOTYyNCAwLTIuNDk0OC0xLjU0MDktMy41OTU1LTMuNTIyMS0zLjU5NTUtMC42
MjM3MSAwLTEuNjE0MyAwLjQwMzU4LTIuMTgzIDEuMTU1NyAwLjEyODQxLTIuMzQ4MSAxLjAwODktMy4xMzY5IDIuMTQ2My0zLjEz
NjkgMC42NjA0IDAgMS4zOTQyIDAuNDAzNTggMS43NjExIDAuODA3MTZsMS42NTEtMS44NzExYy0wLjc3MDQ3LTAuNzcwNDctMS45
ODEyLTEuNDY3Ni0zLjYzMjItMS40Njc2LTIuNDk0OCAwLTQuODA2MiAyLjAxNzktNC44MDYyIDYuMjM3MXMyLjMxMTQgNS44MzM1
IDQuNTQ5NCA1LjgzMzV6bS0wLjA3MzM4LTIuMzQ4MWMtMC41Njg2OCAwLTEuMjY1OC0wLjM4NTI0LTEuNTIyNi0yLjAxNzkgMC4z
NjY4OS0wLjY5NzA5IDAuOTM1NTctMC45OTA2IDEuNDg1OS0wLjk5MDYgMC42NjA0IDAgMS4yODQxIDAuMjc1MTYgMS4yODQxIDEu
Mzk0MiAwIDEuMjI5MS0wLjU4NzAyIDEuNjE0My0xLjI0NzQgMS42MTQzeiIgZmlsbD0iIzAwMTAzMCIgc3Ryb2tlPSJub25lIi8+
CiAgIDwvZz4KICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoMTUuNTE1KSIgYXJpYS1sYWJlbD0iMiI+CiAgICA8cGF0aCBkPSJtOTgu
MDM1IDI2Ny45NWg1LjA0NjF2LTEuMzk5OGgtMS40NDVjLTAuMzM4NjcgMC0wLjgzNTM4IDAuMDQ1Mi0xLjE5NjYgMC4wOTAzIDEu
MTYyOC0xLjIxOTIgMi4yOTE2LTIuNTA2MSAyLjI5MTYtMy43MTQgMC0xLjM3NzItMC45NTk1NS0yLjI4MDQtMi4zNzA3LTIuMjgw
NC0xLjAyNzMgMC0xLjY5MzMgMC4zODM4Mi0yLjQwNDUgMS4xNDAybDAuOTAzMTEgMC44OTE4MmMwLjM2MTI0LTAuMzgzODIgMC43
NTYzNi0wLjczMzc4IDEuMjc1Ni0wLjczMzc4IDAuNjIwODkgMCAxLjAxNiAwLjM4MzgzIDEuMDE2IDEuMDgzNyAwIDEuMDE2LTEu
Mjg2OSAyLjI0NjUtMy4xMTU3IDMuOTczN3oiIGZpbGw9IiMwMDEwMzAiIGZpbGwtb3BhY2l0eT0iLjk3MjU1IiBzdHJva2U9Im5v
bmUiLz4KICAgPC9nPgogICA8ZyB0cmFuc2Zvcm09InJvdGF0ZSgtMTEuMDMzKSIgYXJpYS1sYWJlbD0iOCI+CiAgICA8cGF0aCBk
PSJtLTM4LjkyIDI5MC43NmMxLjI3NDIgMCAyLjEyMzctMC43NDA4MyAyLjEyMzctMS43MDg4IDAtMC44Mzk2Mi0wLjUwMzc3LTEu
MzAzOS0xLjA4NjYtMS42Mjk4di0wLjAzOTVjMC40MDQ5OS0wLjI5NjMzIDAuODM5NjEtMC44MTk4NSAwLjgzOTYxLTEuNDQyMiAw
LTEuMDE3NC0wLjcyMTA4LTEuNjk5LTEuODQ3MS0xLjY5OS0xLjA4NjYgMC0xLjg5NjUgMC42NTE5My0xLjg5NjUgMS42NjkzIDAg
MC42NjE4MSAwLjM4NTIzIDEuMTI2MSAwLjg2OTI0IDEuNDcxOHYwLjAzOTVjLTAuNTkyNjcgMC4zMTYwOS0xLjEzNTkgMC44Mjk3
NC0xLjEzNTkgMS42MTAxIDAgMS4wMTc0IDAuOTA4NzYgMS43Mjg2IDIuMTMzNiAxLjcyODZ6bTAuNDE0ODctMy42NjQ2Yy0wLjcw
MTMyLTAuMjc2NTgtMS4yNjQ0LTAuNTUzMTYtMS4yNjQ0LTEuMTg1MyAwLTAuNTQzMjggMC4zNzUzNi0wLjg1OTM2IDAuODU5Mzct
MC44NTkzNiAwLjU4Mjc5IDAgMC45Mjg1MSAwLjQwNDk4IDAuOTI4NTEgMC45NTgxNCAwIDAuMzk1MTEtMC4xODc2OCAwLjc1MDcx
LTAuNTIzNTIgMS4wODY2em0tMC4zOTUxMSAyLjg1NDdjLTAuNjQyMDYgMC0xLjE1NTctMC40MTQ4Ni0xLjE1NTctMS4wMzcyIDAt
MC40ODQwMSAwLjI4NjQ2LTAuODg5IDAuNjgxNTctMS4xNzU1IDAuODQ5NDkgMC4zNDU3MiAxLjUxMTMgMC41OTI2NyAxLjUxMTMg
MS4yNzQyIDAgMC41ODI3OS0wLjQzNDYyIDAuOTM4MzktMS4wMzcyIDAuOTM4Mzl6IiBmaWxsPSIjMDAxMDMwIiBmaWxsLW9wYWNp
dHk9Ii45NDExOCIgc3Ryb2tlPSJub25lIi8+CiAgIDwvZz4KICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoNi41MDA4KSIgYXJpYS1s
YWJlbD0iMyI+CiAgICA8cGF0aCBkPSJtMzkuMzAyIDI4My42NGMxLjAzMjkgMCAxLjg4ODEtMC41NzU3MyAxLjg4ODEtMS41NTc5
IDAtMC43MTEyLTAuNDgyNi0xLjE2ODQtMS4xMTc2LTEuMzM3N3YtMC4wMzM5YzAuNTg0Mi0wLjIyODYgMC45Mzk4LTAuNjM1IDAu
OTM5OC0xLjIzNjEgMC0wLjkxNDQtMC43MTEyLTEuNDIyNC0xLjc0NDEtMS40MjI0LTAuNjQzNDcgMC0xLjE1OTkgMC4yNzA5My0x
LjYxNzEgMC42NzczM2wwLjQ5OTUzIDAuNjAxMTRjMC4zMzAyLTAuMzA0OCAwLjY2MDQtMC41MDggMS4wODM3LTAuNTA4IDAuNDkx
MDcgMCAwLjc5NTg3IDAuMjcwOTMgMC43OTU4NyAwLjcxOTY3IDAgMC40OTk1My0wLjM0NzEzIDAuODYzNi0xLjQwNTUgMC44NjM2
djAuNzExMmMxLjIyNzcgMCAxLjU4MzMgMC4zNTU2IDEuNTgzMyAwLjkxNDQgMCAwLjUwOC0wLjQwNjQgMC44MTI4LTAuOTkwNiAw
LjgxMjgtMC41NDE4NyAwLTAuOTU2NzMtMC4yNjI0Ny0xLjI3ODUtMC41OTI2N2wtMC40NjU2NyAwLjYyNjUzYzAuMzgxIDAuNDIz
MzQgMC45NTY3MyAwLjc2MiAxLjgyODggMC43NjJ6IiBmaWxsPSIjMDAxMDMwIiBmaWxsLW9wYWNpdHk9Ii44Nzg0MyIgc3Ryb2tl
PSJub25lIi8+CiAgIDwvZz4KICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoOC4zNTYpIiBhcmlhLWxhYmVsPSIxIj4KICAgIDxwYXRo
IGQ9Im00Ni40MDUgMjY4LjloMy4yNDI3di0wLjc5NTg3aC0xLjA1ODN2LTQuNTg4OWgtMC43MjgxM2MtMC4zMzg2NyAwLjIwMzIt
MC43MTEyIDAuMzM4NjYtMS4yNDQ2IDAuNDQwMjZ2MC42MDk2aDAuOTkwNnYzLjUzOTFoLTEuMjAyM3oiIGZpbGw9IiMwMDEwMzAi
IGZpbGwtb3BhY2l0eT0iLjc1Mjk0IiBzdHJva2U9Im5vbmUiLz4KICAgPC9nPgogICA8ZyB0cmFuc2Zvcm09InJvdGF0ZSgxMi44
NjEpIiBhcmlhLWxhYmVsPSI4Ij4KICAgIDxwYXRoIGQ9Im04NS4wMzYgMjYxLjYzYzEuMDkyMiAwIDEuODIwMy0wLjYzNSAxLjgy
MDMtMS40NjQ3IDAtMC43MTk2Ny0wLjQzMTgtMS4xMTc2LTAuOTMxMzMtMS4zOTd2LTAuMDMzOWMwLjM0NzEzLTAuMjU0IDAuNzE5
NjctMC43MDI3MyAwLjcxOTY3LTEuMjM2MSAwLTAuODcyMDctMC42MTgwNy0xLjQ1NjMtMS41ODMzLTEuNDU2My0wLjkzMTMzIDAt
MS42MjU2IDAuNTU4OC0xLjYyNTYgMS40MzA5IDAgMC41NjcyNiAwLjMzMDIgMC45NjUyIDAuNzQ1MDcgMS4yNjE1djAuMDMzOWMt
MC41MDggMC4yNzA5My0wLjk3MzY3IDAuNzExMi0wLjk3MzY3IDEuMzgwMSAwIDAuODcyMDcgMC43Nzg5MyAxLjQ4MTcgMS44Mjg4
IDEuNDgxN3ptMC4zNTU2LTMuMTQxMWMtMC42MDExMy0wLjIzNzA3LTEuMDgzNy0wLjQ3NDE0LTEuMDgzNy0xLjAxNiAwLTAuNDY1
NjcgMC4zMjE3My0wLjczNjYgMC43MzY2LTAuNzM2NiAwLjQ5OTUzIDAgMC43OTU4NyAwLjM0NzEzIDAuNzk1ODcgMC44MjEyNiAw
IDAuMzM4NjctMC4xNjA4NyAwLjY0MzQ3LTAuNDQ4NzMgMC45MzEzNHptLTAuMzM4NjcgMi40NDY5Yy0wLjU1MDMzIDAtMC45OTA2
LTAuMzU1Ni0wLjk5MDYtMC44ODkgMC0wLjQxNDg2IDAuMjQ1NTMtMC43NjIgMC41ODQyLTEuMDA3NSAwLjcyODEzIDAuMjk2MzMg
MS4yOTU0IDAuNTA4IDEuMjk1NCAxLjA5MjIgMCAwLjQ5OTUzLTAuMzcyNTMgMC44MDQzMy0wLjg4OSAwLjgwNDMzeiIgZmlsbD0i
IzAwMTAzMCIgZmlsbC1vcGFjaXR5PSIuNjI3NDUiIHN0cm9rZT0ibm9uZSIvPgogICA8L2c+CiAgIDxnIHRyYW5zZm9ybT0icm90
YXRlKDQuMzA5OSkiIGFyaWEtbGFiZWw9IjUiPgogICAgPHBhdGggZD0ibTQ2LjM0MSAyODkuNDljMC45OTA2IDAgMS44OTY1LTAu
Njc3MzQgMS44OTY1LTEuODU0MiAwLTEuMTU5OS0wLjc3MDQ3LTEuNjg0OS0xLjY5MzMtMS42ODQ5LTAuMjc5NCAwLTAuNDgyNiAw
LjA2NzctMC43MTEyIDAuMTc3OGwwLjExMDA3LTEuMzAzOWgyLjAzMnYtMC44MjEyN2gtMi44Nzg3bC0wLjE2MDg3IDIuNjU4NSAw
LjQ2NTY3IDAuMjk2MzNjMC4zMjE3My0wLjIxMTY3IDAuNTE2NDctMC4zMDQ4IDAuODYzNi0wLjMwNDggMC41OTI2NyAwIDAuOTkw
NiAwLjM2NDA3IDAuOTkwNiAxLjAwNzUgMCAwLjY1MTk0LTAuNDQwMjcgMS4wMzI5LTEuMDQxNCAxLjAzMjktMC41NDE4NyAwLTAu
OTM5OC0wLjI3MDk0LTEuMjYxNS0wLjU3NTc0bC0wLjQ0ODczIDAuNjI2NTRjMC4zOTc5MyAwLjM5NzkzIDAuOTY1MiAwLjc0NTA3
IDEuODM3MyAwLjc0NTA3eiIgZmlsbD0iIzAwMTAzMCIgZmlsbC1vcGFjaXR5PSIuNTAxOTYiIHN0cm9rZT0ibm9uZSIvPgogICA8
L2c+CiAgPC9nPgogIDxnIGZpbGw9IiMwMDEwMzAiIGZpbGwtb3BhY2l0eT0iLjM3NjQ3IiBzdHJva2U9IiMwMDAiIHN0cm9rZS13
aWR0aD0iLjI2NDU4cHgiIGFyaWEtbGFiZWw9IjMiPgogICA8cGF0aCBkPSJtOS44ODU5IDI5My40NmMxLjAzMjkgMCAxLjg4ODEt
MC41NzU3NCAxLjg4ODEtMS41NTc5IDAtMC43MTEyLTAuNDgyNi0xLjE2ODQtMS4xMTc2LTEuMzM3N3YtMC4wMzM5YzAuNTg0Mi0w
LjIyODYgMC45Mzk4LTAuNjM1IDAuOTM5OC0xLjIzNjEgMC0wLjkxNDQtMC43MTEyLTEuNDIyNC0xLjc0NDEtMS40MjI0LTAuNjQz
NDcgMC0xLjE1OTkgMC4yNzA5My0xLjYxNzEgMC42NzczM2wwLjQ5OTUzIDAuNjAxMTNjMC4zMzAyLTAuMzA0OCAwLjY2MDQtMC41
MDggMS4wODM3LTAuNTA4IDAuNDkxMDcgMCAwLjc5NTg3IDAuMjcwOTQgMC43OTU4NyAwLjcxOTY3IDAgMC40OTk1My0wLjM0NzEz
IDAuODYzNi0xLjQwNTUgMC44NjM2djAuNzExMmMxLjIyNzcgMCAxLjU4MzMgMC4zNTU2IDEuNTgzMyAwLjkxNDQgMCAwLjUwOC0w
LjQwNjQgMC44MTI4LTAuOTkwNiAwLjgxMjgtMC41NDE4NyAwLTAuOTU2NzMtMC4yNjI0Ny0xLjI3ODUtMC41OTI2N2wtMC40NjU2
NyAwLjYyNjU0YzAuMzgxIDAuNDIzMzMgMC45NTY3MyAwLjc2MiAxLjgyODggMC43NjJ6IiBmaWxsPSIjMDAxMDMwIiBmaWxsLW9w
YWNpdHk9Ii4zNzY0NyIgc3Ryb2tlPSJub25lIi8+CiAgPC9nPgogIDxnIGZpbGw9Im5vbmUiIHN0cm9rZT0iIzAwMCIgc3Ryb2tl
LXdpZHRoPSIuMjY0NThweCI+CiAgIDxnIHRyYW5zZm9ybT0icm90YXRlKC0xMS4zNTIpIiBhcmlhLWxhYmVsPSIwIj4KICAgIDxw
YXRoIGQ9Im0tNTEuNDcxIDI3Ni4xN2MxLjExNzYgMCAxLjgyODgtMC45OTkwNyAxLjgyODgtMi44MTk0IDAtMS44MTE5LTAuNzEx
Mi0yLjc2ODYtMS44Mjg4LTIuNzY4NnMtMS44Mjg4IDAuOTQ4MjctMS44Mjg4IDIuNzY4NiAwLjcxMTIgMi44MTk0IDEuODI4OCAy
LjgxOTR6bTAtMC43NjJjLTAuNTE2NDcgMC0wLjg5NzQ3LTAuNTMzNC0wLjg5NzQ3LTIuMDU3NHMwLjM4MS0yLjAwNjYgMC44OTc0
Ny0yLjAwNjZjMC41MjQ5MyAwIDAuODk3NDcgMC40ODI2IDAuODk3NDcgMi4wMDY2cy0wLjM3MjUzIDIuMDU3NC0wLjg5NzQ3IDIu
MDU3NHoiIGZpbGw9IiMwMDEwMzAiIGZpbGwtb3BhY2l0eT0iLjI1MDk4IiBzdHJva2U9Im5vbmUiLz4KICAgPC9nPgogICA8ZyB0
cmFuc2Zvcm09InJvdGF0ZSgyMi41MDYpIiBhcmlhLWxhYmVsPSI3Ij4KICAgIDxwYXRoIGQ9Im0xMTguMjEgMjQzLjA4aDAuOTkw
NmMwLjA5MzEtMi4wOTk3IDAuMzEzMjctMy4yMjU4IDEuNTc0OC00Ljc5MjF2LTAuNTkyNjdoLTMuNjE1M3YwLjgyMTI3aDIuNTQ4
NWMtMS4wNDE0IDEuNDQ3OC0xLjQwNTUgMi42NTAxLTEuNDk4NiA0LjU2MzV6IiBmaWxsPSIjMDAxMDMwIiBmaWxsLW9wYWNpdHk9
Ii4xMjU0OSIgc3Ryb2tlPSJub25lIi8+CiAgIDwvZz4KICAgPGcgdHJhbnNmb3JtPSJyb3RhdGUoLTkuNzI3MykiIGFyaWEtbGFi
ZWw9IjEiPgogICAgPHBhdGggZD0ibS0xOC4yOTkgMjgyLjc5aDMuMjQyN3YtMC43OTU4N2gtMS4wNTgzdi00LjU4ODloLTAuNzI4
MTNjLTAuMzM4NjcgMC4yMDMyLTAuNzExMiAwLjMzODY3LTEuMjQ0NiAwLjQ0MDI3djAuNjA5NmgwLjk5MDZ2My41MzkxaC0xLjIw
MjN6IiBmaWxsPSIjMDAxMDMwIiBmaWxsLW9wYWNpdHk9Ii4wNjI3NDUiIHN0cm9rZT0ibm9uZSIvPgogICA8L2c+CiAgPC9nPgog
IDxnIGZpbGw9IiMyNDEwMzAiIGFyaWEtbGFiZWw9Ii4iPgogICA8cGF0aCBkPSJtMjAuOTIgMjgzLjk4YzAuNjU0NzYgMCAxLjEy
ODktMC41MTkyOSAxLjEyODktMS4xNzQgMC0wLjY1NDc2LTAuNDc0MTMtMS4xNzQtMS4xMjg5LTEuMTc0LTAuNjU0NzYgMC0xLjEy
ODkgMC41MTkyOS0xLjEyODkgMS4xNzQgMCAwLjY1NDc1IDAuNDc0MTMgMS4xNzQgMS4xMjg5IDEuMTc0eiIgZmlsbD0iIzAwMTAz
MCIvPgogIDwvZz4KIDwvZz4KPC9zdmc+Cg==
")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]
#![cfg_attr(unsafe_in_unsafe, warn(unsafe_op_in_unsafe_fn))]
#![cfg_attr(not(unsafe_in_unsafe), allow(unused_unsafe))]
// allowed to deal with e.g. 1i32.into(): c_long which can be i32 or i64
#![allow(clippy::useless_conversion)]
// matches! requires rustc 1.42
#![allow(clippy::match_like_matches_macro)]
#[macro_use]
mod macros;
mod ext;
#[cfg(any(feature = "integer", feature = "float"))]
mod misc;
mod ops_prim;
#[cfg(all(feature = "serde", any(feature = "integer", feature = "float")))]
mod serdeize;

pub mod ops;

/**
Assigns to a number from another value.

# Examples

Implementing the trait:

```rust
use rug::Assign;
struct I(i32);
impl Assign<i16> for I {
    fn assign(&mut self, rhs: i16) {
        self.0 = rhs.into();
    }
}
let mut i = I(0);
i.assign(42_i16);
assert_eq!(i.0, 42);
```

Performing an assignment operation using the trait:

```rust
# #[cfg(feature = "integer")] {
use rug::{Assign, Integer};
let mut i = Integer::from(15);
assert_eq!(i, 15);
i.assign(23);
assert_eq!(i, 23);
# }
```
*/
pub trait Assign<Src = Self> {
    /// Peforms the assignement.
    fn assign(&mut self, src: Src);
}

#[cfg(feature = "integer")]
/**
Completes an [incomplete-computation value][icv].

# Examples

Implementing the trait:

```rust
use rug::{Complete, Integer};
struct LazyPow4<'a>(&'a Integer);
impl Complete for LazyPow4<'_> {
    type Completed = Integer;
    fn complete(self) -> Integer {
        self.0.clone().square().square()
    }
}

assert_eq!(LazyPow4(&Integer::from(3)).complete(), 3i32.pow(4));
```

Completing an [incomplete-computation value][icv]:

```rust
use rug::{Complete, Integer};
let incomplete = Integer::fibonacci(12);
let complete = incomplete.complete();
assert_eq!(complete, 144);
```

[icv]: crate#incomplete-computation-values
*/
pub trait Complete {
    /// The type of the completed operation.
    type Completed;

    /// Completes the operation.
    fn complete(self) -> Self::Completed;
}

#[cfg(feature = "integer")]
pub mod integer;
#[cfg(feature = "integer")]
pub use crate::integer::big::Integer;

#[cfg(feature = "rational")]
pub mod rational;
#[cfg(feature = "rational")]
pub use crate::rational::big::Rational;

#[cfg(feature = "float")]
pub mod float;
#[cfg(feature = "float")]
pub use crate::float::big::Float;

#[cfg(feature = "complex")]
pub mod complex;
#[cfg(feature = "complex")]
pub use crate::complex::big::Complex;

#[cfg(feature = "rand")]
pub mod rand;

#[cfg(any(feature = "integer", feature = "float"))]
mod static_assertions {
    use core::mem;
    use gmp_mpfr_sys::gmp::{limb_t, LIMB_BITS, NAIL_BITS, NUMB_BITS};

    static_assert!(NAIL_BITS == 0);
    static_assert!(NUMB_BITS == LIMB_BITS);
    static_assert!(cfg!(target_pointer_width = "32") ^ cfg!(target_pointer_width = "64"));
    static_assert!(cfg!(gmp_limb_bits_32) ^ cfg!(gmp_limb_bits_64));
    #[cfg(gmp_limb_bits_64)]
    static_assert!(NUMB_BITS == 64);
    #[cfg(gmp_limb_bits_32)]
    static_assert!(NUMB_BITS == 32);
    static_assert!(NUMB_BITS % 8 == 0);
    static_assert!(mem::size_of::<limb_t>() == NUMB_BITS as usize / 8);
}

#[cfg(all(test, any(feature = "integer", feature = "float")))]
mod tests {
    #[cfg(any(feature = "rational", feature = "float"))]
    use core::{f32, f64};
    use core::{i128, i16, i32, i64, i8, u128, u16, u32, u64, u8};

    pub const U8: &[u8] = &[0, 1, 100, 101, i8::MAX as u8 + 1, u8::MAX];
    pub const I8: &[i8] = &[i8::MIN, -101, -100, -1, 0, 1, 100, 101, i8::MAX];
    pub const U16: &[u16] = &[0, 1, 1000, 1001, i16::MAX as u16 + 1, u16::MAX];
    pub const I16: &[i16] = &[i16::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, i16::MAX];
    pub const U32: &[u32] = &[0, 1, 1000, 1001, i32::MAX as u32 + 1, u32::MAX];
    pub const I32: &[i32] = &[i32::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, i32::MAX];
    pub const U64: &[u64] = &[
        0,
        1,
        1000,
        1001,
        i32::MAX as u64 + 1,
        u32::MAX as u64 + 1,
        u64::MAX,
    ];
    pub const I64: &[i64] = &[
        i64::MIN,
        -(u32::MAX as i64) - 1,
        i32::MIN as i64 - 1,
        -1001,
        -1000,
        -1,
        0,
        1,
        1000,
        1001,
        i32::MAX as i64 + 1,
        u32::MAX as i64 + 1,
        i64::MAX,
    ];
    pub const U128: &[u128] = &[
        0,
        1,
        1000,
        1001,
        i32::MAX as u128 + 1,
        u32::MAX as u128 + 1,
        i64::MAX as u128 + 1,
        u64::MAX as u128 + 1,
        u128::MAX,
    ];
    pub const I128: &[i128] = &[
        i128::MIN,
        -(u64::MAX as i128) - 1,
        i64::MIN as i128 - 1,
        -(u32::MAX as i128) - 1,
        i32::MIN as i128 - 1,
        -1001,
        -1000,
        -1,
        0,
        1,
        1000,
        1001,
        i32::MAX as i128 + 1,
        u32::MAX as i128 + 1,
        i64::MAX as i128 + 1,
        u64::MAX as i128 + 1,
        i128::MAX,
    ];
    #[cfg(any(feature = "rational", feature = "float"))]
    pub const F32: &[f32] = &[
        -f32::NAN,
        f32::NEG_INFINITY,
        f32::MIN,
        -12.0e30,
        -2.0,
        -1.0 - f32::EPSILON,
        -1.0,
        -f32::MIN_POSITIVE,
        -f32::MIN_POSITIVE * f32::EPSILON,
        -0.0,
        0.0,
        f32::MIN_POSITIVE * f32::EPSILON,
        f32::MIN_POSITIVE,
        1.0,
        1.0 + f32::EPSILON,
        2.0,
        12.0e30,
        f32::MAX,
        f32::INFINITY,
        f32::NAN,
    ];
    #[cfg(any(feature = "rational", feature = "float"))]
    pub const F64: &[f64] = &[
        -f64::NAN,
        f64::NEG_INFINITY,
        f64::MIN,
        -12.0e43,
        -2.0,
        -1.0 - f64::EPSILON,
        -1.0,
        -f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE * f64::EPSILON,
        -0.0,
        0.0,
        f64::MIN_POSITIVE * f64::EPSILON,
        f64::MIN_POSITIVE,
        1.0,
        1.0 + f64::EPSILON,
        2.0,
        12.0e43,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
}
