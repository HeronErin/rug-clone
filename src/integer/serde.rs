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

use Integer;
use serde::de::{Deserialize, Deserializer, Error as DeError};
use serde::ser::{Serialize, Serializer};
use serdeize::{self, Data, PrecReq, PrecVal};

impl Serialize for Integer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let prec = PrecVal::Zero;
        let radix = if self.significant_bits() <= 32 {
            10
        } else {
            16
        };
        let value = self.to_string_radix(radix);
        serdeize::serialize("Integer", &Data { prec, radix, value }, serializer)
    }
}

impl<'de> Deserialize<'de> for Integer {
    fn deserialize<D>(deserializer: D) -> Result<Integer, D::Error>
    where
        D: Deserializer<'de>,
    {
        let Data { prec, radix, value } =
            serdeize::deserialize("Integer", PrecReq::Zero, deserializer)?;
        match prec {
            PrecVal::Zero => {}
            _ => unreachable!(),
        }
        Integer::from_str_radix(&value, radix).map_err(DeError::custom)
    }
}

#[cfg(test)]
mod tests {
    use {Assign, Integer};
    use serde_test::{self, Token};

    enum Check {
        SerDe,
        De,
    }

    fn check_tokens(
        i: &Integer,
        radix: i32,
        value: &'static str,
        check: Check,
    ) {
        let tokens = [
            Token::Struct {
                name: "Integer",
                len: 2,
            },
            Token::Str("radix"),
            Token::I32(radix),
            Token::Str("value"),
            Token::Str(value),
            Token::StructEnd,
        ];
        match check {
            Check::SerDe => serde_test::assert_tokens(i, &tokens),
            Check::De => serde_test::assert_de_tokens(i, &tokens),
        }
    }

    #[test]
    fn check() {
        let mut i = Integer::new();
        check_tokens(&i, 10, "0", Check::SerDe);

        i.assign(-0xffff_ffff_i64);
        check_tokens(&i, 10, "-4294967295", Check::SerDe);
        check_tokens(&i, 16, "-ffffffff", Check::De);

        i = i.abs() + 1;
        check_tokens(&i, 16, "100000000", Check::SerDe);
        check_tokens(&i, 10, "4294967296", Check::De);
    }
}
