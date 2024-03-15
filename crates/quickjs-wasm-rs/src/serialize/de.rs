use crate::js_binding::{
    properties::Properties,
    value::{JSValueRef, JSValueType},
};
use crate::serialize::err::{Error, Result};
use anyhow::anyhow;
use serde::de::{self, Error as SerError};
use serde::forward_to_deserialize_any;

impl SerError for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::Custom(anyhow!(msg.to_string()))
    }
}

/// `Deserializer` is a deserializer for `JSValueRef` values, implementing the `serde::Deserializer` trait.
///
/// This struct is responsible for converting `JSValueRef`, into Rust types using the Serde deserialization framework.
///
/// # Lifetime
///
/// The lifetime parameter `'de` represents the lifetime of the reference to the `JSValueRef`.
/// This ensures that the `Deserializer` cannot outlive the JavaScript value it is deserializing.
///
/// # Example
///
/// ```
/// // Assuming you have a JSValueRef instance named value containing an i32
/// let mut deserializer = Deserializer::from(value);
///
/// // Use deserializer to deserialize the JavaScript value into a Rust type
/// let number: i32 = serde::Deserialize::deserialize(deserializer)?;
/// ```
pub struct Deserializer<'de> {
    value: JSValueRef<'de>,
}

impl<'de> From<JSValueRef<'de>> for Deserializer<'de> {
    fn from(value: JSValueRef<'de>) -> Self {
        Self { value }
    }
}
impl Deserializer<'_> {
    fn deserialize_number<'de, V>(&mut self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        if let Ok(uint) = u64::try_from(&self.value) {
            return visitor.visit_u64(uint);
        }
        if let Ok(int) = i64::try_from(&self.value) {
            return visitor.visit_i64(int);
        }
        if let Ok(float) = f64::try_from(&self.value) {
            return visitor.visit_f64(float);
        }

        unreachable!()
    }
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        match self.value.type_of() {
            JSValueType::Int | JSValueType::BigInt | JSValueType::Float | JSValueType::BigFloat => {
                self.deserialize_number(visitor)
            }
            JSValueType::Bool => visitor.visit_bool(bool::try_from(&self.value).unwrap()),
            JSValueType::Null | JSValueType::Undefined => visitor.visit_unit(),
            JSValueType::String => visitor.visit_str(<&str>::try_from(&self.value).unwrap()),
            JSValueType::Array => {
                let val = self.value.get_property("length")?;
                let length = u64::try_from(&val).unwrap() as u32;
                let seq = self.value.clone();

                visitor.visit_seq(SeqAccess {
                    de: self,
                    length,
                    seq,
                    index: 0,
                })
            }
            JSValueType::ArrayBuffer => {
                visitor.visit_bytes(<&[u8]>::try_from(&self.value).unwrap())
            }
            JSValueType::Object => {
                let properties = self.value.properties()?;

                visitor.visit_map(MapAccess {
                    de: self,
                    properties,
                })
            }
            _ => Err(Error::Custom(anyhow!(
                "Couldn't deserialize value: {:?}",
                self.value
            ))),
        }
    }

    fn is_human_readable(&self) -> bool {
        false
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        match self.value.type_of() {
            JSValueType::Null | JSValueType::Undefined => visitor.visit_none(),
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: de::Visitor<'de>,
    {
        unimplemented!()
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf unit unit_struct seq tuple
        tuple_struct map struct identifier ignored_any
    }
}

struct MapAccess<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    properties: Properties<'de>,
}

impl<'a, 'de> de::MapAccess<'de> for MapAccess<'a, 'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: de::DeserializeSeed<'de>,
    {
        if let Some(key) = self.properties.next_key()? {
            self.de.value = key;
            seed.deserialize(&mut *self.de).map(Some)
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: de::DeserializeSeed<'de>,
    {
        self.de.value = self.properties.next_value()?;
        seed.deserialize(&mut *self.de)
    }
}

struct SeqAccess<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
    seq: JSValueRef<'de>,
    length: u32,
    index: u32,
}

impl<'a, 'de> de::SeqAccess<'de> for SeqAccess<'a, 'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: de::DeserializeSeed<'de>,
    {
        if self.index < self.length {
            self.de.value = self.seq.get_indexed_property(self.index)?;
            self.index += 1;
            seed.deserialize(&mut *self.de).map(Some)
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::Deserializer as ValueDeserializer;
    use crate::js_binding::constants::MAX_SAFE_INTEGER;
    use crate::js_binding::context::JSContextRef;
    use crate::js_binding::value::JSValueRef;
    use serde::de::DeserializeOwned;
    use serde_bytes::ByteBuf;

    fn deserialize_value<T>(v: JSValueRef) -> T
    where
        T: DeserializeOwned,
    {
        let mut deserializer = ValueDeserializer::from(v);
        T::deserialize(&mut deserializer).unwrap()
    }

    #[test]
    fn test_null() {
        let context = JSContextRef::default();
        let val = context.null_value().unwrap();
        deserialize_value::<()>(val);
    }

    #[test]
    fn test_undefined() {
        let context = JSContextRef::default();
        let val = context.undefined_value().unwrap();
        deserialize_value::<()>(val);
    }

    #[test]
    fn test_nan() {
        let context = JSContextRef::default();
        let val = context.value_from_f64(f64::NAN).unwrap();
        let actual = deserialize_value::<f64>(val);
        assert!(actual.is_nan());
    }

    #[test]
    fn test_infinity() {
        let context = JSContextRef::default();
        let val = context.value_from_f64(f64::INFINITY).unwrap();
        let actual = deserialize_value::<f64>(val);
        assert!(actual.is_infinite() && actual.is_sign_positive());
    }

    #[test]
    fn test_negative_infinity() {
        let context = JSContextRef::default();
        let val = context.value_from_f64(f64::NEG_INFINITY).unwrap();
        let actual = deserialize_value::<f64>(val);
        assert!(actual.is_infinite() && actual.is_sign_negative());
    }

    #[test]
    fn test_map_always_converts_keys_to_string() {
        // Sanity check to make sure the quickjs VM always store object
        // object keys as a string an not a numerical value.
        let context = JSContextRef::default();
        context.eval_global("main", "var a = {1337: 42};").unwrap();
        let val = context.global_object().unwrap().get_property("a").unwrap();

        let actual = deserialize_value::<BTreeMap<String, i32>>(val);

        assert_eq!(42, *actual.get("1337").unwrap())
    }

    #[test]
    #[should_panic]
    fn test_map_does_not_support_non_string_keys() {
        // Sanity check to make sure it's not possible to deserialize
        // to a map where keys are not strings (e.g. numerical value).
        let context = JSContextRef::default();
        context.eval_global("main", "var a = {1337: 42};").unwrap();
        let val = context.global_object().unwrap().get_property("a").unwrap();

        deserialize_value::<BTreeMap<i32, i32>>(val);
    }

    #[test]
    fn test_u64_bounds() {
        let context = JSContextRef::default();

        let max = u64::MAX;
        let val = context.value_from_u64(max).unwrap();
        let actual = deserialize_value::<u64>(val);
        assert_eq!(max, actual);

        let min = u64::MIN;
        let val = context.value_from_u64(min).unwrap();
        let actual = deserialize_value::<u64>(val);
        assert_eq!(min, actual);
    }

    #[test]
    fn test_i64_bounds() {
        let context = JSContextRef::default();

        let max = i64::MAX;
        let val = context.value_from_i64(max).unwrap();
        let actual = deserialize_value::<i64>(val);
        assert_eq!(max, actual);

        let min = i64::MIN;
        let val = context.value_from_i64(min).unwrap();
        let actual = deserialize_value::<i64>(val);
        assert_eq!(min, actual);
    }

    #[test]
    fn test_float_to_integer_conversion() {
        let context = JSContextRef::default();

        let expected = MAX_SAFE_INTEGER - 1;
        let val = context.value_from_f64(expected as _).unwrap();
        let actual = deserialize_value::<i64>(val);
        assert_eq!(expected, actual);

        let expected = MAX_SAFE_INTEGER + 1;
        let val = context.value_from_f64(expected as _).unwrap();
        let actual = deserialize_value::<f64>(val);
        assert_eq!(expected as f64, actual);
    }

    #[test]
    fn test_u32_upper_bound() {
        let context = JSContextRef::default();
        let expected = u32::MAX;
        let val = context.value_from_u32(expected).unwrap();
        let actual = deserialize_value::<u32>(val);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_u32_lower_bound() {
        let context = JSContextRef::default();
        let expected = i32::MAX as u32 + 1;
        let val = context.value_from_u32(expected).unwrap();
        let actual = deserialize_value::<u32>(val);
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_array_buffer() {
        let context = JSContextRef::default();

        context
            .eval_global(
                "main",
                "var a = new Uint8Array(3);\
                 a[0] = 42;\
                 a[1] = 0;\
                 a[2] = 255;
                 a = a.buffer;",
            )
            .unwrap();

        let val = deserialize_value::<ByteBuf>(
            context.global_object().unwrap().get_property("a").unwrap(),
        )
        .into_vec();

        assert_eq!(vec![42u8, 0, 255], val);
    }

    #[test]
    fn test_array() {
        let context = JSContextRef::default();

        context.eval_global("main", "var a = [1, 2, 3];").unwrap();

        let val = deserialize_value::<Vec<u8>>(
            context.global_object().unwrap().get_property("a").unwrap(),
        );

        assert_eq!(vec![1, 2, 3], val);
    }
}
