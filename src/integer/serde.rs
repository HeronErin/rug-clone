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

use serde::de::{Deserialize, Deserializer, Error as DeError};
use serde::ser::{Serialize, Serializer};
use serdeize::{self, Data, PrecReq, PrecVal};
use {Assign, Integer};

impl Serialize for Integer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let prec = PrecVal::Zero;
        let radix = if self.significant_bits() <= 32 { 10 } else { 16 };
        let value = self.to_string_radix(radix);
        let data = Data { prec, radix, value };
        serdeize::serialize("Integer", &data, serializer)
    }
}

impl<'de> Deserialize<'de> for Integer {
    fn deserialize<D>(deserializer: D) -> Result<Integer, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (radix, value) = de_data(deserializer)?;
        let p = Integer::parse_radix(&value, radix).map_err(DeError::custom)?;
        Ok(Integer::from(p))
    }

    fn deserialize_in_place<D>(
        deserializer: D,
        place: &mut Integer,
    ) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        let (radix, value) = de_data(deserializer)?;
        let p = Integer::parse_radix(&value, radix).map_err(DeError::custom)?;
        place.assign(p);
        Ok(())
    }
}

fn de_data<'de, D>(deserializer: D) -> Result<(i32, String), D::Error>
where
    D: Deserializer<'de>,
{
    let Data { prec, radix, value } =
        serdeize::deserialize("Integer", PrecReq::Zero, deserializer)?;
    match prec {
        PrecVal::Zero => {}
        _ => unreachable!(),
    }
    serdeize::check_range("radix", radix, 2, 36)?;
    Ok((radix, value))
}

#[cfg(test)]
mod tests {
    use cast::cast;
    use {Assign, Integer};

    fn assert(a: &Integer, b: &Integer) {
        assert_eq!(a, b);
    }

    enum Check<'a> {
        SerDe(&'a Integer),
        De(&'a Integer),
        DeError(&'a str),
    }

    impl<'a> Check<'a> {
        fn check(self, radix: i32, value: &'static str) {
            use byteorder::{LittleEndian, WriteBytesExt};
            #[allow(unused_imports)]
            use serde_test::{self, Token};
            use serdeize::test::*;
            use std::io::Write;
            let tokens = [
                Token::Struct { name: "Integer", len: 2 },
                Token::Str("radix"),
                Token::I32(radix),
                Token::Str("value"),
                Token::Str(value),
                Token::StructEnd,
            ];
            let json = json!({
                "radix": radix,
                "value": value,
            });
            let mut bincode = Vec::<u8>::new();
            bincode.write_i32::<LittleEndian>(radix).unwrap();
            bincode.write_u64::<LittleEndian>(cast(value.len())).unwrap();
            bincode.write_all(value.as_bytes()).unwrap();
            match self {
                Check::SerDe(i) => {
                    serde_test::assert_tokens(i, &tokens);
                    json_assert_value(i, &json, assert);
                    let in_place = Integer::from(0xbad);
                    bincode_assert_value(i, &bincode, assert, in_place);
                }
                Check::De(i) => {
                    serde_test::assert_de_tokens(i, &tokens);
                    json_assert_de_value(i, json, assert);
                    bincode_assert_de_value(i, &bincode, assert);
                }
                Check::DeError(msg) => {
                    serde_test::assert_de_tokens_error::<Integer>(&tokens, msg);
                }
            }
        }
    }

    #[test]
    fn check() {
        Check::DeError("radix 1 less than minimum 2").check(1, "0");
        Check::DeError("radix 37 greater than maximum 36").check(37, "0");

        let mut i = Integer::new();
        Check::SerDe(&i).check(10, "0");
        Check::De(&i).check(10, "+0");
        Check::De(&i).check(10, "-00");

        i.assign(-0xffff_ffff_i64);
        Check::SerDe(&i).check(10, "-4294967295");
        Check::De(&i).check(16, "-ffffffff");

        i = i.abs() + 1;
        Check::SerDe(&i).check(16, "100000000");
        Check::De(&i).check(10, "4294967296");
    }
}
