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

#[cfg(test)]
mod tests {
    use {Assign, Complex};
    use float::Special;
    use serde_test::{self, Token};

    enum Check {
        SerDe,
        De,
    }

    fn check_tokens(
        c: &Complex,
        radix: i32,
        value: &'static str,
        check: Check,
    ) {
        let prec = c.prec();
        let tokens = [
            Token::Struct {
                name: "Complex",
                len: 3,
            },
            Token::Str("prec"),
            Token::Tuple { len: 2 },
            Token::U32(prec.0),
            Token::U32(prec.1),
            Token::TupleEnd,
            Token::Str("radix"),
            Token::I32(radix),
            Token::Str("value"),
            Token::Str(value),
            Token::StructEnd,
        ];
        match check {
            Check::SerDe => serde_test::assert_tokens(c.as_ord(), &tokens),
            Check::De => serde_test::assert_de_tokens(c.as_ord(), &tokens),
        }
    }

    #[test]
    fn check() {
        let mut c = Complex::new((40, 32));
        check_tokens(&c, 10, "(0.0 0.0)", Check::SerDe);

        c = -c;
        check_tokens(&c, 10, "(-0.0 -0.0)", Check::SerDe);
        check_tokens(&c, 16, "(-0 -0)", Check::De);

        c.assign((Special::Nan, 15.0));
        check_tokens(&c, 10, "(NaN 1.5000000000e1)", Check::SerDe);
        check_tokens(&c, 10, "(+@nan@ 15)", Check::De);
        c = -c;
        check_tokens(&c, 10, "(-NaN -1.5000000000e1)", Check::SerDe);

        c.assign((15.0, Special::Nan));
        check_tokens(&c, 16, "(f.0000000000 @NaN@)", Check::SerDe);
        check_tokens(&c, 10, "(1.5e1 nan)", Check::De);
        check_tokens(&c, 15, "(1.0@1 @nan@)", Check::De);
    }
}
