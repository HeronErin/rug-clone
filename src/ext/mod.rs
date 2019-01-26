// Copyright © 2016–2019 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

#[cfg(feature = "integer")]
pub mod gmp;
#[cfg(all(feature = "integer", gmp_limb_bits_32))]
pub(self) mod gmp32;
#[cfg(all(feature = "integer", gmp_limb_bits_64))]
pub(self) mod gmp64;
#[cfg(feature = "complex")]
pub mod mpc;
#[cfg(feature = "float")]
pub mod mpfr;
