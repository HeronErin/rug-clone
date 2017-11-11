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

use Complex;
use complex::OrdComplex;
use serde::de::{Deserialize, Deserializer, Error as DeError};
use serde::ser::{Serialize, Serializer};
use serdeize::{self, Data, PrecReq, PrecVal};

impl Serialize for Complex {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let prec = self.prec();
        let radix = if (prec.0 <= 32 || !self.real().is_normal())
            && (prec.1 <= 32 || !self.imag().is_normal())
        {
            10
        } else {
            16
        };
        let prec = PrecVal::Two(prec);
        let value = self.to_string_radix(radix, None);
        serdeize::serialize("Complex", &Data { prec, radix, value }, serializer)
    }
}

impl<'de> Deserialize<'de> for Complex {
    fn deserialize<D>(deserializer: D) -> Result<Complex, D::Error>
    where
        D: Deserializer<'de>,
    {
        let Data { prec, radix, value } =
            serdeize::deserialize("Complex", PrecReq::Two, deserializer)?;
        let prec = match prec {
            PrecVal::Two(two) => two,
            _ => unreachable!(),
        };
        Complex::from_str_radix(&value, radix, prec).map_err(DeError::custom)
    }
}

impl Serialize for OrdComplex {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_complex().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for OrdComplex {
    fn deserialize<D>(deserializer: D) -> Result<OrdComplex, D::Error>
    where
        D: Deserializer<'de>,
    {
        Complex::deserialize(deserializer).map(From::from)
    }
}
