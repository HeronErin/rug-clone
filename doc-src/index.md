% Arbitrary-precision numbers

The [`rug`][rug] crate provides integers and floating-point numbers
with arbitrary precision and correct rounding. Its main features are:

* big [integers][rug int] with arbitrary precision,
* big [rational numbers][rug rat] with arbitrary precision,
* multi-precision [floating-point numbers][rug flo] with correct
  rounding, and
* multi-precision [complex numbers][rug comp] with correct rounding.
	
The `rug` crate depends on the low-level bindings in the
[`gmp-mpfr-sys`][sys] crate. This should be transparent on GNU/Linux
and macOS, but may need some work on Windows. See the crate's
[documentation][sys] for some details. The `gmp-mpfr-sys` crate
provides RUST FFI bindings for:

* the [GNU Multiple Precision Arithmetic Library][gmp home] (GMP),
* the [GNU MPFR Library][mpfr home], a library for multiple-precision
  floating-point computations, and
* [GNU MPC][mpc home], a library for the arithmetic of complex numbers
  with arbitrarily high precision.

## License

These crates are free software: you can redistribute them and/or
modify them under the terms of the GNU Lesser General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version. See the full text of
the [GNU LGPL][lgpl] and [GNU GPL][gpl] for details.

[gmp home]:  https://gmplib.org/
[gpl]:       https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]:      https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpc home]:  http://www.multiprecision.org/
[mpfr home]: http://www.mpfr.org/
[rug com]:   https://tspiteri.gitlab.io/rug/rug/Complex.html
[rug flo]:   https://tspiteri.gitlab.io/rug/rug/Float.html
[rug int]:   https://tspiteri.gitlab.io/rug/rug/Integer.html
[rug rat]:   https://tspiteri.gitlab.io/rug/rug/Rational.html
[rug]:       https://tspiteri.gitlab.io/rug/rug/index.html
[sys]:       https://tspiteri.gitlab.io/rug/gmp_mpfr_sys/index.html
