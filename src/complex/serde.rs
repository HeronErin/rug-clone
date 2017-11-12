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
use float;
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
        serdeize::check_range(
            "real precision",
            prec.0,
            float::prec_min(),
            float::prec_max(),
        )?;
        serdeize::check_range(
            "imaginary precision",
            prec.1,
            float::prec_min(),
            float::prec_max(),
        )?;
        serdeize::check_range("radix", radix, 2, 36)?;
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
    use float::{self, Special};
    use serde_test::{self, Token};

    enum Check<'a> {
        SerDe(&'a Complex),
        De(&'a Complex),
        DeError((u32, u32), &'a str),
    }

    impl<'a> Check<'a> {
        fn check(self, radix: i32, value: &'static str) {
            let prec = match &self {
                &Check::SerDe(c) | &Check::De(c) => c.prec(),
                &Check::DeError(p, _) => p,
            };
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
            match self {
                Check::SerDe(c) => {
                    serde_test::assert_tokens(c.as_ord(), &tokens)
                }
                Check::De(c) => {
                    serde_test::assert_de_tokens(c.as_ord(), &tokens)
                }
                Check::DeError(_, msg) => {
                    serde_test::assert_de_tokens_error::<Complex>(&tokens, msg)
                }
            }
        }
    }

    #[test]
    fn check() {
        let prec_min = float::prec_min();
        let real_prec_err =
            format!("real precision 0 less than minimum {}", prec_min);
        let imag_prec_err =
            format!("imaginary precision 0 less than minimum {}", prec_min);
        Check::DeError((0, 32), &real_prec_err).check(10, "0");
        Check::DeError((40, 0), &imag_prec_err).check(10, "0");
        Check::DeError((40, 32), "radix 1 less than minimum 2").check(1, "0");
        Check::DeError((40, 32), "radix 37 greater than maximum 36")
            .check(37, "0");

        let mut c = Complex::new((40, 32));
        Check::SerDe(&c).check(10, "(0.0 0.0)");
        Check::De(&c).check(10, "0");

        c = -c;
        Check::SerDe(&c).check(10, "(-0.0 -0.0)");
        Check::De(&c).check(16, "(-0 -0)");

        c.assign((Special::Nan, 15.0));
        Check::SerDe(&c).check(10, "(NaN 1.5000000000e1)");
        Check::De(&c).check(10, "(+@nan@ 15)");
        c = -c;
        Check::SerDe(&c).check(10, "(-NaN -1.5000000000e1)");

        c.assign((15.0, Special::Nan));
        Check::SerDe(&c).check(16, "(f.0000000000 @NaN@)");
        Check::De(&c).check(10, "(1.5e1 nan)");
        Check::De(&c).check(15, "(1.0@1 @nan@)");
    }
}
