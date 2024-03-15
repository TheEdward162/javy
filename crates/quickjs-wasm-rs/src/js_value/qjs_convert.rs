use std::collections::HashMap;

use anyhow::{bail, Result};

use super::JSValue;
use crate::js_binding::{
    context::JSContextRef,
    value::{JSValueRef, JSValueType},
};

/// Converts a reference to QuickJS value represented by `quickjs_wasm_rs::JSValueRef` to a `JSValue`.
///
/// # Arguments
///
/// * `val` - a `JSValueRef` to be converted to a `JSValue`
///
/// # Returns
///
/// * `anyhow::Result<JSValue>`
///
/// # Example
///
/// ```
/// // Assuming `qjs_val` is a `JSValueRef` pointing to a QuickJS string
/// let js_val = from_qjs_value(qjs_val).unwrap();
/// assert_eq!(js_val, "hello".into());
/// ```
pub fn from_qjs_value(val: &JSValueRef) -> Result<JSValue> {
    let js_val = match val.type_of() {
        JSValueType::Null => JSValue::Null,
        JSValueType::Undefined => JSValue::Undefined,
        JSValueType::Bool => JSValue::Bool(val.try_into()?),
        JSValueType::Int | JSValueType::BigInt => JSValue::Int(i64::try_from(val)?.try_into()?),
        JSValueType::Float | JSValueType::BigFloat => JSValue::Float(f64::try_from(val)?),
        JSValueType::String => JSValue::String(<&str>::try_from(val)?.to_owned()),
        JSValueType::Array => {
            let array_len = u64::try_from(&val.get_property("length")?)? as usize;
            let mut result = Vec::with_capacity(array_len);
            for i in 0..array_len {
                result.push(from_qjs_value(&val.get_indexed_property(i.try_into()?)?)?);
            }
            JSValue::Array(result)
        }
        JSValueType::ArrayBuffer => JSValue::ArrayBuffer(<&[u8]>::try_from(val)?.to_vec()),
        JSValueType::Object => {
            let mut result = HashMap::new();
            let mut properties = val.properties()?;
            while let Some(property_key) = properties.next_key()? {
                let property_key = <&str>::try_from(&property_key)?;
                let property_value = from_qjs_value(&val.get_property(property_key)?)?;
                result.insert(property_key.to_string(), property_value);
            }

            JSValue::Object(result)
        }
        t => bail!("unhandled type: {:?}", t),
    };

    Ok(js_val)
}

/// Converts a reference to a `JSValue` to a `quickjs_wasm_rs::JSValueRef`.
///
/// # Arguments
///
/// * `context` - a reference to a `quickjs_wasm_rs::JSContextRef`. The `JSValueRef` is created for this JS context.
/// * `val` - a reference to a `JSValue` to be converted to a `JSValueRef`
///
/// # Returns
///
/// * `anyhow::Result<JSValueRef>`
///
/// # Example
///
/// ```
/// let context = JSContextRef::default();
/// let js_val = "hello".into();
/// let qjs_val = to_qjs_value(&context, &js_val).unwrap();
/// ```
pub fn to_qjs_value<'a>(context: &'a JSContextRef, val: &JSValue) -> Result<JSValueRef<'a>> {
    let qjs_val = match val {
        JSValue::Undefined => context.undefined_value()?,
        JSValue::Null => context.null_value()?,
        JSValue::Bool(flag) => context.value_from_bool(*flag)?,
        JSValue::Int(val) => context.value_from_i32(*val)?,
        JSValue::Float(val) => context.value_from_f64(*val)?,
        JSValue::String(val) => context.value_from_str(val)?,
        JSValue::ArrayBuffer(buffer) => context.array_buffer_value(buffer)?,
        JSValue::Array(values) => {
            let arr = context.array_value()?;
            for v in values.iter() {
                arr.append_property(to_qjs_value(context, v)?)?
            }
            arr
        }
        JSValue::Object(hashmap) => {
            let obj = context.object_value()?;
            for (key, value) in hashmap {
                obj.set_property(key.clone(), to_qjs_value(context, value)?)?
            }
            obj
        }
    };
    Ok(qjs_val)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_qjs_null() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "null").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, JSValue::Null);
    }

    #[test]
    fn test_from_qjs_undefined() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "undefined").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, JSValue::Undefined);
    }

    #[test]
    fn test_from_qjs_bool() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "true").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, true.into());
    }

    #[test]
    fn test_from_qjs_int() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "42").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, 42.into());
    }

    #[test]
    fn test_from_qjs_float() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "42.5").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, 42.5.into());
    }

    #[test]
    fn test_from_qjs_string() {
        let context = JSContextRef::default();
        let qjs_val = context
            .eval_global("test.js", "const h = 'hello'; h")
            .unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, "hello".into());
    }

    #[test]
    fn test_from_qjs_array() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "[1, 2, 3]").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(
            js_val,
            vec![JSValue::Int(1), JSValue::Int(2), JSValue::Int(3)].into()
        );
    }

    #[test]
    fn test_from_qjs_array_buffer() {
        let context = JSContextRef::default();
        let qjs_val = context
            .eval_global("test.js", "new ArrayBuffer(8)")
            .unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(js_val, [0_u8; 8].as_ref().into());
    }

    #[test]
    fn test_from_qjs_object() {
        let context = JSContextRef::default();
        let qjs_val = context.eval_global("test.js", "({a: 1, b: 2})").unwrap();
        let js_val = from_qjs_value(&qjs_val).unwrap();
        assert_eq!(
            js_val,
            HashMap::from([
                ("a".to_string(), JSValue::Int(1)),
                ("b".to_string(), JSValue::Int(2))
            ])
            .into()
        )
    }

    #[test]
    fn test_to_qjs_null() {
        let context = JSContextRef::default();
        let js_val = JSValue::Null;
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(qjs_val.type_of(), JSValueType::Null);
    }

    #[test]
    fn test_to_qjs_undefined() {
        let context = JSContextRef::default();
        let js_val = JSValue::Undefined;
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(qjs_val.type_of(), JSValueType::Undefined);
    }

    #[test]
    fn test_to_qjs_bool() {
        let context = JSContextRef::default();
        let js_val = true.into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(qjs_val.type_of(), JSValueType::Bool);
    }

    #[test]
    fn test_to_qjs_int() {
        let context = JSContextRef::default();
        let js_val = 42.into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(i64::try_from(&qjs_val).unwrap(), 42);
    }

    #[test]
    fn test_to_qjs_float() {
        let context = JSContextRef::default();
        let js_val = 42.3.into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(f64::try_from(&qjs_val).unwrap(), 42.3);
    }

    #[test]
    fn test_to_qjs_string() {
        let context = JSContextRef::default();
        let js_val = "hello".into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(<&str>::try_from(&qjs_val).unwrap(), "hello");
    }

    #[test]
    fn test_to_qjs_array_buffer() {
        let context = JSContextRef::default();
        let js_val = "hello".as_bytes().into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(<&[u8]>::try_from(&qjs_val).unwrap(), "hello".as_bytes());
    }

    #[test]
    fn test_to_qjs_array() {
        let context = JSContextRef::default();
        let js_val = vec![JSValue::Int(1), JSValue::Int(2)].into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(
            i64::try_from(&qjs_val.get_property("0").unwrap()).unwrap(),
            1
        );
        assert_eq!(
            u64::try_from(&qjs_val.get_property("1").unwrap()).unwrap(),
            2
        );
    }

    #[test]
    fn test_to_qjs_object() {
        let context = JSContextRef::default();
        let js_val = HashMap::from([
            ("a".to_string(), JSValue::Int(-1)),
            ("b".to_string(), JSValue::Int(2)),
        ])
        .into();
        let qjs_val = to_qjs_value(&context, &js_val).unwrap();
        assert_eq!(
            i64::try_from(&qjs_val.get_property("a").unwrap()).unwrap(),
            -1
        );
        assert_eq!(
            u64::try_from(&qjs_val.get_property("b").unwrap()).unwrap(),
            2
        );
    }

    #[test]
    fn test_convert_vec() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "[1, 2, 3]")?;

        let expected: Vec<JSValue> = vec![1.into(), 2.into(), 3.into()];

        assert_eq!(val.to_string(), "1,2,3");

        let val_ref = &val;
        let arg = from_qjs_value(val_ref)?;
        assert_eq!(arg, JSValue::Array(expected));

        Ok(())
    }

    #[test]
    fn test_convert_hashmap() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "({a: 1, b: 2, c: 3})")?;

        let expected = HashMap::from([
            ("a".to_string(), 1.into()),
            ("b".to_string(), 2.into()),
            ("c".to_string(), 3.into()),
        ]);

        assert_eq!(val.to_string(), "[object Object]");

        let val_ref = &val;
        let arg = from_qjs_value(val_ref)?;
        assert_eq!(arg, JSValue::Object(expected));

        Ok(())
    }
}
