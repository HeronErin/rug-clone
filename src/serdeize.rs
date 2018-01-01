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

use serde::de::{Deserialize, Deserializer, Error as DeError, MapAccess,
                SeqAccess, Visitor};
use serde::ser::{SerializeStruct, Serializer};
use std::fmt::{Display, Formatter, Result as FmtResult};

pub enum PrecReq {
    #[cfg(feature = "integer")] Zero,
    #[cfg(feature = "float")] One,
    #[cfg(feature = "complex")] Two,
}

pub enum PrecVal {
    #[cfg(feature = "integer")] Zero,
    #[cfg(feature = "float")] One(u32),
    #[cfg(feature = "complex")] Two((u32, u32)),
}

pub struct Data {
    pub prec: PrecVal,
    pub radix: i32,
    pub value: String,
}

pub fn serialize<S>(
    name: &'static str,
    data: &Data,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let mut state = match data.prec {
        #[cfg(feature = "integer")]
        PrecVal::Zero => serializer.serialize_struct(name, 2)?,
        #[cfg(feature = "float")]
        PrecVal::One(one) => {
            let mut state = serializer.serialize_struct(name, 3)?;
            state.serialize_field("prec", &one)?;
            state
        }
        #[cfg(feature = "complex")]
        PrecVal::Two(two) => {
            let mut state = serializer.serialize_struct(name, 3)?;
            state.serialize_field("prec", &two)?;
            state
        }
    };
    state.serialize_field("radix", &data.radix)?;
    state.serialize_field("value", &data.value)?;
    state.end()
}

const FIELDS: &[&str] = &["radix", "value"];

enum Field {
    Radix,
    Value,
}

struct FieldVisitor;

impl<'de> Visitor<'de> for FieldVisitor {
    type Value = Field;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("`radix` or `value`")
    }

    fn visit_str<E>(self, value: &str) -> Result<Field, E>
    where
        E: DeError,
    {
        match value {
            "radix" => Ok(Field::Radix),
            "value" => Ok(Field::Value),
            _ => Err(DeError::unknown_field(value, FIELDS)),
        }
    }
}

impl<'de> Deserialize<'de> for Field {
    fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(FieldVisitor)
    }
}

const PREC_FIELDS: &[&str] = &["prec", "radix", "value"];

enum PrecField {
    Prec,
    Field(Field),
}

struct PrecFieldVisitor;

impl<'de> Visitor<'de> for PrecFieldVisitor {
    type Value = PrecField;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str("`prec`, `radix` or `value`")
    }

    fn visit_str<E>(self, value: &str) -> Result<PrecField, E>
    where
        E: DeError,
    {
        match value {
            "prec" => Ok(PrecField::Prec),
            "radix" => Ok(PrecField::Field(Field::Radix)),
            "value" => Ok(PrecField::Field(Field::Value)),
            _ => Err(DeError::unknown_field(value, PREC_FIELDS)),
        }
    }
}

impl<'de> Deserialize<'de> for PrecField {
    fn deserialize<D>(deserializer: D) -> Result<PrecField, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(PrecFieldVisitor)
    }
}

struct BigVisitor(&'static str, PrecReq);

impl<'de> Visitor<'de> for BigVisitor {
    type Value = Data;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        formatter.write_str(self.0)
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<Data, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let prec = match self.1 {
            #[cfg(feature = "integer")]
            PrecReq::Zero => PrecVal::Zero,
            #[cfg(feature = "float")]
            PrecReq::One => PrecVal::One(seq.next_element()?
                .ok_or_else(|| DeError::invalid_length(0, &self))?),
            #[cfg(feature = "complex")]
            PrecReq::Two => PrecVal::Two(seq.next_element()?
                .ok_or_else(|| DeError::invalid_length(0, &self))?),
        };
        let prec_count = match self.1 {
            #[cfg(feature = "integer")]
            PrecReq::Zero => 0,
            #[cfg(feature = "float")]
            PrecReq::One => 1,
            #[cfg(feature = "complex")]
            PrecReq::Two => 1,
        };
        let radix = seq.next_element()?
            .ok_or_else(|| DeError::invalid_length(prec_count, &self))?;
        let value = seq.next_element()?
            .ok_or_else(|| DeError::invalid_length(prec_count + 1, &self))?;
        Ok(Data { prec, radix, value })
    }

    fn visit_map<V>(self, mut map: V) -> Result<Data, V::Error>
    where
        V: MapAccess<'de>,
    {
        #[cfg(not(feature = "float"))]
        let prec = Some(PrecVal::Zero);
        #[cfg(feature = "float")]
        let mut prec = match self.1 {
            #[cfg(feature = "integer")]
            PrecReq::Zero => Some(PrecVal::Zero),
            PrecReq::One => None,
            #[cfg(feature = "complex")]
            PrecReq::Two => None,
        };
        let mut radix = None;
        let mut value = None;
        while let Some(key) = match self.1 {
            #[cfg(feature = "integer")]
            PrecReq::Zero => map.next_key()?.map(PrecField::Field),
            #[cfg(feature = "float")]
            PrecReq::One => map.next_key()?,
            #[cfg(feature = "complex")]
            PrecReq::Two => map.next_key()?,
        } {
            match key {
                #[cfg(not(feature = "float"))]
                PrecField::Prec => unreachable!(),
                #[cfg(feature = "float")]
                PrecField::Prec => {
                    if prec.is_some() {
                        return Err(DeError::duplicate_field("prec"));
                    }
                    prec = match self.1 {
                        #[cfg(feature = "integer")]
                        PrecReq::Zero => unreachable!(),
                        PrecReq::One => Some(PrecVal::One(map.next_value()?)),
                        #[cfg(feature = "complex")]
                        PrecReq::Two => Some(PrecVal::Two(map.next_value()?)),
                    }
                }
                PrecField::Field(Field::Radix) => {
                    if radix.is_some() {
                        return Err(DeError::duplicate_field("radix"));
                    }
                    radix = Some(map.next_value()?);
                }
                PrecField::Field(Field::Value) => {
                    if value.is_some() {
                        return Err(DeError::duplicate_field("value"));
                    }
                    value = Some(map.next_value()?);
                }
            }
        }
        let prec = prec.ok_or_else(|| DeError::missing_field("prec"))?;
        let radix = radix.ok_or_else(|| DeError::missing_field("radix"))?;
        let value = value.ok_or_else(|| DeError::missing_field("value"))?;
        Ok(Data { prec, radix, value })
    }
}

pub fn deserialize<'de, D>(
    name: &'static str,
    prec_req: PrecReq,
    deserializer: D,
) -> Result<Data, D::Error>
where
    D: Deserializer<'de>,
{
    let fields = match prec_req {
        #[cfg(feature = "integer")]
        PrecReq::Zero => FIELDS,
        #[cfg(feature = "float")]
        PrecReq::One => PREC_FIELDS,
        #[cfg(feature = "complex")]
        PrecReq::Two => PREC_FIELDS,
    };
    deserializer.deserialize_struct(name, fields, BigVisitor(name, prec_req))
}

pub fn check_range<T, D>(
    name: &'static str,
    val: T,
    min: T,
    max: T,
) -> Result<(), D>
where
    T: Display + Ord,
    D: DeError,
{
    if val < min {
        Err(DeError::custom(format_args!(
            "{} {} less than minimum {}",
            name, val, min,
        )))
    } else if val > max {
        Err(DeError::custom(format_args!(
            "{} {} greater than maximum {}",
            name, val, max,
        )))
    } else {
        Ok(())
    }
}
