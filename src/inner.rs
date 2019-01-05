// Copyright © 2016–2018 University of Malta

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

pub trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

// inner_mut() is unsafe as it can be used to change the internal
// state, e.g. Integer::inner_mut() will give an &mut gmp::mpz_t,
// which can be used to modify the pointer inside.
pub trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}
