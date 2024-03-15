use crate::js_binding::{context::JSContextRef, value::JSValueRef};
use crate::serialize::err::{Error, Result};
use anyhow::anyhow;

use serde::{ser, ser::Error as SerError, Serialize};

/// `Serializer` is a serializer for `JSValueRef` values, implementing the `serde::Serializer` trait.
///
/// This struct is responsible for converting Rust types into `JSValueRef` using the Serde
/// serialization framework.
///
/// # Lifetime
///
/// The lifetime parameter `'c` represents the lifetime of the reference to the `JSContextRef`.
/// This ensures that the `Serializer` cannot outlive the JavaScript context it is associated with.
///
/// # Example
///
/// ```
/// // Assuming you have a JSContextRef instance named context
/// let serializer = Serializer::from_context(context)?;
/// let value: JSValueRef = serializer.serialize_u32(42)?;
/// ```
pub struct Serializer<'c> {
    pub context: &'c JSContextRef,
    pub value: JSValueRef<'c>,
    pub key: JSValueRef<'c>,
}

impl SerError for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::Custom(anyhow!(msg.to_string()))
    }
}

impl<'c> Serializer<'c> {
    pub fn from_context(context: &'c JSContextRef) -> Result<Self> {
        Ok(Self {
            context,
            value: context.undefined_value()?,
            key: context.undefined_value()?,
        })
    }
}

impl<'a> ser::Serializer for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_i8(self, v: i8) -> Result<()> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_i16(self, v: i16) -> Result<()> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_i32(self, v: i32) -> Result<()> {
        self.value = self.context.value_from_i32(v)?;
        Ok(())
    }

    fn serialize_i64(self, v: i64) -> Result<()> {
        self.value = self.context.value_from_i64(v)?;
        Ok(())
    }

    fn serialize_u8(self, v: u8) -> Result<()> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_u16(self, v: u16) -> Result<()> {
        self.serialize_i32(i32::from(v))
    }

    fn serialize_u32(self, v: u32) -> Result<()> {
        // NOTE: See optimization note in serialize_f64.
        self.serialize_f64(f64::from(v))
    }

    fn serialize_u64(self, v: u64) -> Result<()> {
        self.value = self.context.value_from_u64(v)?;
        Ok(())
    }

    fn serialize_f32(self, v: f32) -> Result<()> {
        // NOTE: See optimization note in serialize_f64.
        self.serialize_f64(f64::from(v))
    }

    fn serialize_f64(self, v: f64) -> Result<()> {
        // NOTE: QuickJS will create a number value backed by an i32 when the value is within
        // the i32::MIN..=i32::MAX as an optimization. Otherwise the value will be backed by a f64.
        self.value = self.context.value_from_f64(v)?;
        Ok(())
    }

    fn serialize_bool(self, b: bool) -> Result<()> {
        self.value = self.context.value_from_bool(b)?;
        Ok(())
    }

    fn serialize_char(self, v: char) -> Result<()> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<()> {
        self.value = self.context.value_from_str(v)?;
        Ok(())
    }

    fn serialize_none(self) -> Result<()> {
        self.serialize_unit()
    }

    fn serialize_unit(self) -> Result<()> {
        self.value = self.context.null_value()?;
        Ok(())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<()> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<()> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        self.value = self.context.array_value()?;
        Ok(self)
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        self.serialize_seq(Some(len))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap> {
        self.value = self.context.object_value()?;
        Ok(self)
    }

    fn serialize_struct(self, _name: &'static str, len: usize) -> Result<Self::SerializeStruct> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        self.serialize_map(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        self.serialize_map(Some(len))
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut object = self.context.object_value()?;
        value.serialize(&mut *self)?;
        std::mem::swap(&mut self.value, &mut object);
        self.value.set_property(variant, object)?;

        Ok(())
    }

    fn serialize_bytes(self, bytes: &[u8]) -> Result<()> {
        self.value = self.context.array_buffer_value(bytes)?;

        Ok(())
    }
}

impl<'a> ser::SerializeSeq for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut element_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut element_serializer)?;
        self.value.append_property(element_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeTuple for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut element_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut element_serializer)?;
        self.value.append_property(element_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeTupleStruct for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut field_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut field_serializer)?;
        self.value.append_property(field_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeTupleVariant for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut field_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut field_serializer)?;
        self.value.append_property(field_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeMap for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut key_serializer = Serializer::from_context(self.context)?;
        key.serialize(&mut key_serializer)?;
        self.key = key_serializer.value;
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut map_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut map_serializer)?;

        let key = match <&str>::try_from(&self.key) {
            Err(_) => return Err(anyhow::anyhow!("map keys must be a string").into()),
            Ok(k) => k,
        };

        self.value.set_property(key, map_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeStruct for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut field_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut field_serializer)?;
        self.value.set_property(key, field_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<'a> ser::SerializeStructVariant for &'a mut Serializer<'_> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let mut field_serializer = Serializer::from_context(self.context)?;
        value.serialize(&mut field_serializer)?;
        self.value.set_property(key, field_serializer.value)?;
        Ok(())
    }

    fn end(self) -> Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::Serializer as ValueSerializer;
    use crate::js_binding::{
        constants::{MAX_SAFE_INTEGER, MIN_SAFE_INTEGER},
        context::JSContextRef,
        value::JSValueType,
    };
    use anyhow::Result;
    use quickcheck::quickcheck;
    use serde::{Serialize, Serializer};
    use serde_bytes::ByteBuf;

    quickcheck! {
        fn test_i16(v: i16) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_i16(v)?;
            Ok(matches!(serializer.value.type_of(), JSValueType::Int))
        }

        fn test_i32(v: i32) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_i32(v)?;
            Ok(matches!(serializer.value.type_of(), JSValueType::Int))
        }

        fn test_i64(v: i64) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_i64(v)?;
            if (MIN_SAFE_INTEGER..=MAX_SAFE_INTEGER).contains(&v) {
                Ok(matches!(serializer.value.type_of(), JSValueType::Int | JSValueType::Float))
            } else {
                Ok(matches!(serializer.value.type_of(), JSValueType::BigInt))
            }
        }

        fn test_u64(v: u64) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_u64(v)?;

            if v <= MAX_SAFE_INTEGER as u64 {
                Ok(matches!(serializer.value.type_of(), JSValueType::Int | JSValueType::Float))
            } else {
                Ok(matches!(serializer.value.type_of(), JSValueType::BigInt))
            }
        }

        fn test_u16(v: u16) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;

            serializer.serialize_u16(v)?;

            Ok(matches!(serializer.value.type_of(), JSValueType::Int))
        }

        fn test_u32(v: u32) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;

            serializer.serialize_u32(v)?;
            // QuickJS optimizes numbers in the range of [i32::MIN..=i32::MAX]
            // as ints
            if v > i32::MAX as u32 {
                Ok(matches!(serializer.value.type_of(), JSValueType::Float))
            } else {
                Ok(matches!(serializer.value.type_of(), JSValueType::Int))
            }
        }

        fn test_f32(v: f32) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_f32(v)?;

            if v == 0.0_f32 {
                if v.is_sign_positive() {
                    return Ok(matches!(serializer.value.type_of(), JSValueType::Int));
                }


                if v.is_sign_negative() {
                    return Ok(matches!(serializer.value.type_of(), JSValueType::Float));
                }
            }

            // The same (int) optimization is happening at this point,
            // but here we need to account for signs
            let zero_fractional_part = v.fract() == 0.0;
            let range = (i32::MIN as f32)..=(i32::MAX as f32);

            if zero_fractional_part && range.contains(&v) {
                Ok(matches!(serializer.value.type_of(), JSValueType::Int))
            } else {
                Ok(matches!(serializer.value.type_of(), JSValueType::Float))
            }
        }

        fn test_f64(v: f64) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_f64(v)?;

            if v == 0.0_f64 {
                if v.is_sign_positive() {
                    return Ok(matches!(serializer.value.type_of(), JSValueType::Int));
                }


                if v.is_sign_negative() {
                    return Ok(matches!(serializer.value.type_of(), JSValueType::Float));
                }
            }

            // The same (int) optimization is happening at this point,
            // but here we need to account for signs
            let zero_fractional_part = v.fract() == 0.0;
            let range = (i32::MIN as f64)..=(i32::MAX as f64);

            if zero_fractional_part && range.contains(&v) {
                Ok(matches!(serializer.value.type_of(), JSValueType::Int))
            } else {
                Ok(matches!(serializer.value.type_of(), JSValueType::Float))
            }
        }

        fn test_bool(v: bool) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_bool(v)?;

            Ok(matches!(serializer.value.type_of(), JSValueType::Bool))
        }

        fn test_str(v: String) -> Result<bool> {
            let context = JSContextRef::default();
            let mut serializer = ValueSerializer::from_context(&context)?;
            serializer.serialize_str(v.as_str())?;

            Ok(matches!(serializer.value.type_of(), JSValueType::String))
        }
    }

    #[test]
    fn test_null() -> Result<()> {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context)?;
        serializer.serialize_unit()?;

        assert_eq!(serializer.value.type_of(), JSValueType::Null);
        Ok(())
    }

    #[test]
    fn test_nan() -> Result<()> {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context)?;
        serializer.serialize_f64(f64::NAN)?;

        assert_eq!(serializer.value.type_of(), JSValueType::Float);
        Ok(())
    }

    #[test]
    fn test_infinity() -> Result<()> {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context)?;
        serializer.serialize_f64(f64::INFINITY)?;

        assert_eq!(serializer.value.type_of(), JSValueType::Float);
        Ok(())
    }

    #[test]
    fn test_negative_infinity() -> Result<()> {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context)?;
        serializer.serialize_f64(f64::NEG_INFINITY)?;

        assert_eq!(serializer.value.type_of(), JSValueType::Float);
        Ok(())
    }

    #[test]
    fn test_map_with_invalid_key_type() {
        // This is technically possible since msgpack supports maps
        // with any other valid msgpack type. However, we try to enforce
        // using `K: String` since it allow transcoding from json<->msgpack.
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context).unwrap();

        let mut map = BTreeMap::new();
        map.insert(42, "bar");
        map.insert(43, "titi");

        let err = map.serialize(&mut serializer).unwrap_err();
        assert_eq!(err.to_string(), "map keys must be a string".to_string());
    }

    #[test]
    fn test_map() {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context).unwrap();

        let mut map = BTreeMap::new();
        map.insert("foo", "bar");
        map.insert("toto", "titi");

        map.serialize(&mut serializer).unwrap();

        assert_eq!(serializer.value.type_of(), JSValueType::Object);
    }

    #[test]
    fn test_struct_into_map() {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context).unwrap();

        #[derive(serde::Serialize)]
        struct MyObject {
            foo: String,
            bar: u32,
        }

        let my_object = MyObject {
            foo: "hello".to_string(),
            bar: 1337,
        };
        my_object.serialize(&mut serializer).unwrap();

        assert_eq!(serializer.value.type_of(), JSValueType::Object);
    }

    #[test]
    fn test_sequence() {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context).unwrap();

        let sequence = vec!["hello", "world"];

        sequence.serialize(&mut serializer).unwrap();

        assert_eq!(serializer.value.type_of(), JSValueType::Array);
    }

    #[test]
    fn test_array_buffer() {
        let context = JSContextRef::default();
        let mut serializer = ValueSerializer::from_context(&context).unwrap();

        ByteBuf::from(vec![42u8, 0, 255])
            .serialize(&mut serializer)
            .unwrap();

        assert_eq!(serializer.value.type_of(), JSValueType::ArrayBuffer);

        assert_eq!(
            <&[u8]>::try_from(&serializer.value).unwrap(),
            &[42u8, 0, 255]
        );
    }
}
