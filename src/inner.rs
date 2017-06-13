// Copyright © 2016–2017 University of Malta

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
// this program. If not, see <http://www.gnu.org/licenses/>.

pub trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

pub trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

pub enum OwnBorrow<'a, T>
where
    T: 'a,
{
    Own(T),
    Borrow(&'a T),
}

impl<'a, T> Inner for OwnBorrow<'a, T>
where
    T: Inner,
{
    type Output = <T as Inner>::Output;
    fn inner(&self) -> &Self::Output {
        match *self {
            OwnBorrow::Own(ref o) => o.inner(),
            OwnBorrow::Borrow(b) => b.inner(),
        }
    }
}
