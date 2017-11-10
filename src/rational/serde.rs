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

use Rational;
use serde::de::{Deserialize, Deserializer, Error as DeError};
use serde::ser::{Serialize, Serializer};
use serdeize::{self, Data, PrecReq, PrecVal};

impl Serialize for Rational {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let prec = PrecVal::Zero;
        let radix = if self.numer().significant_bits() <= 32
            && self.denom().significant_bits() <= 32
        {
            10
        } else {
            16
        };
        let value = self.to_string_radix(radix);
        serdeize::serialize(
            "Rational",
            &Data { prec, radix, value },
            serializer,
        )
    }
}

impl<'de> Deserialize<'de> for Rational {
    fn deserialize<D>(deserializer: D) -> Result<Rational, D::Error>
    where
        D: Deserializer<'de>,
    {
        let Data { prec, radix, value } =
            serdeize::deserialize("Rational", PrecReq::Zero, deserializer)?;
        match prec {
            PrecVal::Zero => {}
            _ => unreachable!(),
        }
        Rational::from_str_radix(&value, radix).map_err(DeError::custom)
    }
}
