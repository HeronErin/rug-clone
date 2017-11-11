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
use float::OrdFloat;
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

impl Serialize for OrdFloat {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.as_float().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for OrdFloat {
    fn deserialize<D>(deserializer: D) -> Result<OrdFloat, D::Error>
    where
        D: Deserializer<'de>,
    {
        Float::deserialize(deserializer).map(From::from)
    }
}

#[cfg(test)]
mod tests {
    use {Assign, Float};
    use float::Special;
    use serde_test::{self, Token};

    enum Check {
        SerDe,
        De,
    }

    fn check_tokens(
        f: &Float,
        prec: u32,
        radix: i32,
        value: &'static str,
        check: Check,
    ) {
        let tokens = [
            Token::Struct {
                name: "Float",
                len: 3,
            },
            Token::Str("prec"),
            Token::U32(prec),
            Token::Str("radix"),
            Token::I32(radix),
            Token::Str("value"),
            Token::Str(value),
            Token::StructEnd,
        ];
        match check {
            Check::SerDe => serde_test::assert_tokens(f.as_ord(), &tokens),
            Check::De => serde_test::assert_de_tokens(f.as_ord(), &tokens),
        }
    }

    #[test]
    fn check() {
        let mut f = Float::new(40);
        check_tokens(&f, 40, 10, "0.0", Check::SerDe);

        f = -f;
        check_tokens(&f, 40, 10, "-0.0", Check::SerDe);
        check_tokens(&f, 40, 16, "-0", Check::De);

        f.assign(Special::Nan);
        check_tokens(&f, 40, 10, "NaN", Check::SerDe);
        check_tokens(&f, 40, 10, "+@nan@", Check::De);
        f = -f;
        check_tokens(&f, 40, 10, "-NaN", Check::SerDe);

        f.assign(15.0);
        check_tokens(&f, 40, 16, "f.0000000000", Check::SerDe);
        check_tokens(&f, 40, 10, "1.5e1", Check::De);
        check_tokens(&f, 40, 15, "1.0@1", Check::De);

        f.set_prec(32);
        check_tokens(&f, 32, 10, "1.5000000000e1", Check::SerDe);
        check_tokens(&f, 32, 16, "f", Check::De);
        check_tokens(&f, 32, 16, "0.f@1", Check::De);
        check_tokens(&f, 32, 15, "1.0@1", Check::De);
    }
}
