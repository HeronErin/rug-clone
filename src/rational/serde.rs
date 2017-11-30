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
            #[cfg(feature = "float")]
            _ => unreachable!(),
        }
        serdeize::check_range("radix", radix, 2, 36)?;
        Rational::from_str_radix(&value, radix).map_err(DeError::custom)
    }
}

#[cfg(test)]
mod tests {
    use {Assign, Rational};
    use serde_test::{self, Token};

    enum Check<'a> {
        SerDe(&'a Rational),
        De(&'a Rational),
        DeError(&'a str),
    }

    impl<'a> Check<'a> {
        fn check(self, radix: i32, value: &'static str) {
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
            match self {
                Check::SerDe(r) => serde_test::assert_tokens(r, &tokens),
                Check::De(r) => serde_test::assert_de_tokens(r, &tokens),
                Check::DeError(msg) => {
                    serde_test::assert_de_tokens_error::<Rational>(&tokens, msg)
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
