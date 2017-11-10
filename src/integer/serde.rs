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
use serde::de::{Deserialize, Deserializer, Error as DeError, MapAccess,
                SeqAccess, Visitor};
use serde::ser::{Serialize, SerializeStruct, Serializer};
use std::fmt;

impl Serialize for Integer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let radix = if self.significant_bits() <= 32 {
            10
        } else {
            16
        };
        let value = self.to_string_radix(radix);
        let mut state = serializer.serialize_struct("Integer", 2)?;
        state.serialize_field("radix", &radix)?;
        state.serialize_field("value", &value)?;
        state.end()
    }
}

const FIELDS: &'static [&'static str] = &["radix", "value"];

enum Field {
    Radix,
    Value,
}

struct FieldVisitor;

impl<'de> Visitor<'de> for FieldVisitor {
    type Value = Field;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
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

struct IntegerVisitor;

impl<'de> Visitor<'de> for IntegerVisitor {
    type Value = Integer;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("struct Integer")
    }

    fn visit_seq<V>(self, mut seq: V) -> Result<Integer, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let radix = seq.next_element()?
            .ok_or_else(|| DeError::invalid_length(0, &self))?;
        if radix < 2 || radix > 36 {
            return Err(DeError::custom(format_args!(
                "radix {} out of range, expected from 2 to 36",
                radix
            )));
        }
        let value: String = seq.next_element()?
            .ok_or_else(|| DeError::invalid_length(1, &self))?;
        Integer::from_str_radix(&value, radix)
            .map_err(|e| DeError::custom(format_args!("{}", e)))
    }

    fn visit_map<V>(self, mut map: V) -> Result<Integer, V::Error>
    where
        V: MapAccess<'de>,
    {
        let mut radix = None;
        let mut value = None;
        while let Some(key) = map.next_key()? {
            match key {
                Field::Radix => {
                    if radix.is_some() {
                        return Err(DeError::duplicate_field("radix"));
                    }
                    let r = map.next_value()?;
                    if r < 2 || r > 36 {
                        return Err(DeError::custom(format_args!(
                            "radix {} out of range, expected from 2 to 36",
                            r
                        )));
                    }
                    radix = Some(r);
                }
                Field::Value => {
                    if value.is_some() {
                        return Err(DeError::duplicate_field("value"));
                    }
                    value = Some(map.next_value()?);
                }
            }
        }
        let radix = radix.ok_or_else(|| DeError::missing_field("radix"))?;
        let value: String =
            value.ok_or_else(|| DeError::missing_field("value"))?;
        Integer::from_str_radix(&value, radix)
            .map_err(|e| DeError::custom(format_args!("{}", e)))
    }
}
impl<'de> Deserialize<'de> for Integer {
    fn deserialize<D>(deserializer: D) -> Result<Integer, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_struct("Integer", FIELDS, IntegerVisitor)
    }
}
