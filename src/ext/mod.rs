// Copyright © 2016–2020 University of Malta

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

#[cfg(feature = "complex")]
pub mod xmpc;
#[cfg(feature = "float")]
pub mod xmpfr;
#[cfg(feature = "rational")]
pub mod xmpq;
#[cfg(feature = "integer")]
pub mod xmpz;
#[cfg(all(feature = "integer", gmp_limb_bits_32))]
mod xmpz32;
#[cfg(all(feature = "integer", gmp_limb_bits_64))]
mod xmpz64;

pub trait RawOption<Raw>: Copy {
    const IS_SOME: bool;
    fn raw(self) -> *const Raw;
    fn raw_or(self, default: *mut Raw) -> *const Raw;
}

impl<Raw> RawOption<Raw> for () {
    const IS_SOME: bool = false;
    #[inline(always)]
    fn raw(self) -> *const Raw {
        panic!("unwrapping ()");
    }
    #[inline(always)]
    fn raw_or(self, default: *mut Raw) -> *const Raw {
        default as *const Raw
    }
}
