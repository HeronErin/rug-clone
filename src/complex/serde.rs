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

use Complex;
use cast::cast;
use complex::OrdComplex;
use float;
use gmp_mpfr_sys::mpfr;
use inner::InnerMut;
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
        let (prec, radix, value) = de_data(deserializer)?;
        Complex::from_str_radix(&value, radix, prec).map_err(DeError::custom)
    }

    fn deserialize_in_place<D>(
        deserializer: D,
        place: &mut Complex,
    ) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        let (prec, radix, value) = de_data(deserializer)?;
        unsafe {
            let parts = place.as_mut_real_imag();
            mpfr::set_prec(parts.0.inner_mut(), cast(prec.0));
            mpfr::set_prec(parts.1.inner_mut(), cast(prec.1));
        }
        place
            .assign_str_radix(&value, radix)
            .map_err(DeError::custom)
    }
}

fn de_data<'de, D>(
    deserializer: D,
) -> Result<((u32, u32), i32, String), D::Error>
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
    Ok((prec, radix, value))
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

    fn deserialize_in_place<D>(
        deserializer: D,
        place: &mut OrdComplex,
    ) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        Complex::deserialize_in_place(deserializer, place.as_complex_mut())
    }
}

#[cfg(test)]
mod tests {
    use {Assign, Complex};
    use bincode;
    use float::{self, Special};
    use serde::Deserialize;
    use serde_json;
    use serde_test;

    fn json_assert_value(c: &Complex, value: &serde_json::Value) {
        let encoded = serde_json::to_string(c).unwrap();
        let decoded: Complex = serde_json::from_str(&encoded).unwrap();
        assert_eq!(c.prec(), decoded.prec());
        assert_eq!(c.as_ord(), decoded.as_ord());

        let decoded_value: serde_json::Value =
            serde_json::from_str(&encoded).unwrap();
        assert_eq!(value, &decoded_value);
    }

    fn json_assert_de_value(c: &Complex, value: serde_json::Value) {
        let decoded: Complex = serde_json::from_value(value).unwrap();
        assert_eq!(c.prec(), decoded.prec());
        assert_eq!(c.as_ord(), decoded.as_ord());
    }

    fn try_bincode(c: &Complex) {
        use bincode::Deserializer;
        use bincode::read_types::SliceReader;
        let encoded = bincode::serialize(&c, bincode::Infinite).unwrap();
        let decoded: Complex = bincode::deserialize(&encoded).unwrap();
        assert_eq!(c.prec(), decoded.prec());
        assert_eq!(c.as_ord(), decoded.as_ord());
        let mut in_place = Complex::new(1);
        let reader = SliceReader::new(&encoded);
        let mut de = Deserializer::new(reader, bincode::Infinite);
        Deserialize::deserialize_in_place(&mut de, &mut in_place).unwrap();
        assert_eq!(c.prec(), in_place.prec());
        assert_eq!(c.as_ord(), in_place.as_ord());
    }

    enum Check<'a> {
        SerDe(&'a Complex),
        De(&'a Complex),
        DeError((u32, u32), &'a str),
    }

    impl<'a> Check<'a> {
        fn check(self, radix: i32, value: &'static str) {
            use serde_test::Token;
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
            let json_value = json!({
                "prec": [prec.0, prec.1],
                "radix": radix,
                "value": value,
            });
            match self {
                Check::SerDe(c) => {
                    serde_test::assert_tokens(c.as_ord(), &tokens);
                    json_assert_value(c, &json_value);
                    try_bincode(c);
                }
                Check::De(c) => {
                    serde_test::assert_de_tokens(c.as_ord(), &tokens);
                    json_assert_de_value(c, json_value);
                }
                Check::DeError(_, msg) => {
                    serde_test::assert_de_tokens_error::<Complex>(&tokens, msg);
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
