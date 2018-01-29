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
        let (radix, value) = de_data(deserializer)?;
        Rational::from_str_radix(&value, radix).map_err(DeError::custom)
    }

    fn deserialize_in_place<D>(
        deserializer: D,
        place: &mut Rational,
    ) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        let (radix, value) = de_data(deserializer)?;
        place
            .assign_str_radix(&value, radix)
            .map_err(DeError::custom)
    }
}

fn de_data<'de, D>(deserializer: D) -> Result<(i32, String), D::Error>
where
    D: Deserializer<'de>,
{
    let Data { prec, radix, value } =
        serdeize::deserialize("Rational", PrecReq::Zero, deserializer)?;
    match prec {
        PrecVal::Zero => {}
        #[cfg(feature = "float")]
        _ => unreachable!(),
    }
    serdeize::check_range("radix", radix, 2, 36)?;
    Ok((radix, value))
}

#[cfg(test)]
mod tests {
    use {Assign, Rational};
    use bincode;
    use serde::Deserialize;
    use serde_json;
    use serde_test;

    enum Check<'a> {
        SerDe(&'a Rational),
        De(&'a Rational),
        DeError(&'a str),
    }

    fn json_assert_value(r: &Rational, value: &serde_json::Value) {
        let encoded = serde_json::to_string(r).unwrap();
        let decoded: Rational = serde_json::from_str(&encoded).unwrap();
        assert_eq!(r, &decoded);

        let decoded_value: serde_json::Value =
            serde_json::from_str(&encoded).unwrap();
        assert_eq!(value, &decoded_value);
    }

    fn json_assert_de_value(r: &Rational, value: serde_json::Value) {
        let decoded: Rational = serde_json::from_value(value).unwrap();
        assert_eq!(r, &decoded);
    }

    fn try_bincode(r: &Rational) {
        use bincode::Deserializer;
        use bincode::read_types::SliceReader;
        let encoded = bincode::serialize(&r, bincode::Infinite).unwrap();
        let decoded: Rational = bincode::deserialize(&encoded).unwrap();
        assert_eq!(r, &decoded);
        let mut in_place = Rational::from((111, 47));
        let reader = SliceReader::new(&encoded);
        let mut de = Deserializer::new(reader, bincode::Infinite);
        Deserialize::deserialize_in_place(&mut de, &mut in_place).unwrap();
        assert_eq!(r, &in_place);
    }

    impl<'a> Check<'a> {
        fn check(self, radix: i32, value: &'static str) {
            use serde_test::Token;
            let tokens = [
                Token::Struct {
                    name: "Rational",
                    len: 2,
                },
                Token::Str("radix"),
                Token::I32(radix),
                Token::Str("value"),
                Token::Str(value),
                Token::StructEnd,
            ];
            let json_value = json!({
                "radix": radix,
                "value": value,
            });
            match self {
                Check::SerDe(r) => {
                    serde_test::assert_tokens(r, &tokens);
                    json_assert_value(r, &json_value);
                    try_bincode(r);
                }
                Check::De(r) => {
                    serde_test::assert_de_tokens(r, &tokens);
                    json_assert_de_value(r, json_value);
                }
                Check::DeError(msg) => {
                    serde_test::assert_de_tokens_error::<Rational>(
                        &tokens,
                        msg,
                    );
                }
            }
        }
    }

    #[test]
    fn check() {
        Check::DeError("radix 1 less than minimum 2").check(1, "0");
        Check::DeError("radix 37 greater than maximum 36").check(37, "0");

        let mut r = Rational::new();
        Check::SerDe(&r).check(10, "0");
        Check::De(&r).check(10, "+0/1");

        r.assign((11_i64, -0xffff_ffff_i64));
        Check::SerDe(&r).check(10, "-11/4294967295");
        Check::De(&r).check(16, "-b/ffffffff");
        Check::De(&r).check(16, "-b0/ffffffff0");

        r.assign((-11_i64, -0x1_0000_0000_i64));
        Check::SerDe(&r).check(16, "b/100000000");
    }
}
