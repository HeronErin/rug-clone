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

use Float;
use serde::de::{Deserialize, Deserializer, Error as DeError};
use serde::ser::{Serialize, Serializer};
use serdeize::{self, Data, PrecReq, PrecVal};

impl Serialize for Float {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let prec = self.prec();
        let radix = if prec <= 32 || !self.is_normal() {
            10
        } else {
            16
        };
        let prec = PrecVal::One(prec);
        let value = self.to_string_radix(radix, None);
        serdeize::serialize("Float", &Data { prec, radix, value }, serializer)
    }
}

impl<'de> Deserialize<'de> for Float {
    fn deserialize<D>(deserializer: D) -> Result<Float, D::Error>
    where
        D: Deserializer<'de>,
    {
        let Data { prec, radix, value } =
            serdeize::deserialize("Float", PrecReq::One, deserializer)?;
        let prec = match prec {
            PrecVal::One(one) => one,
            _ => unreachable!(),
        };
        Float::from_str_radix(&value, radix, prec).map_err(DeError::custom)
    }
}
