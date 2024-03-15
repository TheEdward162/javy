use std::fmt;
use std::fmt::Debug;
use std::ops::RangeInclusive;

use super::context::JSContextRef;
use super::exception::Exception;
use super::properties::Properties;
use anyhow::{self, Result};
use quickjs_wasm_sys::{
    size_t as JS_size_t, JSValue as JSValueRaw, JS_BigIntToInt64, JS_BigIntToUint64, JS_Call,
    JS_DefinePropertyValueStr, JS_DefinePropertyValueUint32, JS_DupValue_Ext, JS_EvalFunction,
    JS_FreeValue_Ext, JS_GetArrayBuffer, JS_GetPropertyStr, JS_GetPropertyUint32, JS_IsArray,
    JS_IsArrayBuffer_Ext, JS_IsFloat64_Ext, JS_IsFunction, JS_ToCStringLen2, JS_ToFloat64,
    JS_ToInt64, JS_PROP_C_W_E, JS_TAG_BIG_FLOAT, JS_TAG_BIG_INT, JS_TAG_BOOL, JS_TAG_EXCEPTION,
    JS_TAG_INT, JS_TAG_NULL, JS_TAG_OBJECT, JS_TAG_STRING, JS_TAG_SYMBOL, JS_TAG_UNDEFINED,
};
use std::borrow::Cow;
use std::ffi::CString;
use std::str;

/// Describes the type of a QuickJS value.
///
/// Note that this is not the same as JavaScript type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum JSValueType {
    Unknown,
    Int,
    Bool,
    Null,
    Undefined,
    Float,
    BigInt,
    BigFloat,
    Symbol,
    String,
    Object,
    Array,
    ArrayBuffer,
    Function,
    Exception,
}
impl JSValueType {
    pub fn is_int(&self) -> bool {
        matches!(self, Self::Int | Self::BigInt)
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float | Self::BigFloat)
    }

    pub fn is_null_or_undefined(&self) -> bool {
        matches!(self, Self::Null | Self::Undefined)
    }
}

/// `JSValueRef` is a wrapper around a QuickJS `JSValue` with a reference to its associated `JSContextRef`.
///
/// This struct provides a safe interface for interacting with JavaScript values in the context of
/// their associated QuickJS execution environment.
///
/// This value might be reference-counted inside QuickJS and thus needs to be cleaned up on Drop.
///
/// # Lifetime
///
/// The lifetime parameter `'a` represents the lifetime of the reference to the `JSContextRef`.
/// This ensures that the `JSValueRef` cannot outlive the context it is associated with, preventing
/// potential use-after-free issues or other unsafe behavior.
pub struct JSValueRef<'a> {
    pub(super) context: &'a JSContextRef,
    value: JSValueRaw,
}
impl<'a> JSValueRef<'a> {
    pub(super) fn new(context: &'a JSContextRef, raw_value: JSValueRaw) -> Result<Self> {
        let value = Self {
            context,
            value: raw_value,
        };

        match value.type_of() {
            JSValueType::Exception => {
                let exception = value.as_exception()?;
                Err(exception.into_error())
            }
            _ => Ok(value),
        }
    }

    /// Creates a new `JSValueRef` from a `u64`, which is QuickJS’s internal representation.
    ///
    /// # Safety
    /// The caller has to ensure that the given value is valid and belongs to the context.
    /// The value must be valid to be freed when `Self` is dropped.
    ///
    /// This function is not part of the crate’s semver API contract.
    #[cfg_attr(feature = "export-sys", visibility::make(pub))]
    pub(super) unsafe fn from_raw(context: &'a JSContextRef, value: JSValueRaw) -> Self {
        Self { context, value }
    }

    /// Returns QuickJS’s internal representation. Note that the value is implicitly tied to the context it came from.
    ///
    /// # Safety
    /// The function is safe to call, but not part of the crate’s semver API contract.
    #[cfg_attr(feature = "export-sys", visibility::make(pub))]
    pub(super) unsafe fn as_raw(&self) -> JSValueRaw {
        self.value
    }

    /// Deconstructs `JSValueRef` into raw parts.
    ///
    /// This will effectively leak the value, so it needs to be reconstructed using [`Self::from_raw`] to be dropped.
    ///
    /// # Safety
    /// The function is safe to call, but not part of the crate’s semver API contract.
    #[cfg_attr(feature = "export-sys", visibility::make(pub))]
    pub(super) unsafe fn into_raw(self) -> (&'a JSContextRef, JSValueRaw) {
        let me = std::mem::ManuallyDrop::new(self);
        (me.context, me.value)
    }

    pub(super) fn eval_function(self) -> Result<Self> {
        // value is being moved into QuickJS, it will be freed there
        let (context, value) = unsafe { self.into_raw() };
        Self::new(context, unsafe { JS_EvalFunction(context.as_raw(), value) })
    }

    /// Calls a JavaScript function with the specified `receiver` and `args`.
    ///
    /// # Arguments
    /// * `receiver`: The object on which the function is called.
    /// * `args`: A slice of [`JSValueRef`] representing the arguments to be
    ///   passed to the function.
    pub fn call(&self, receiver: &Self, args: &[Self]) -> Result<Self> {
        let args: Vec<JSValueRaw> = args.iter().map(|v| v.value).collect();
        let return_val = unsafe {
            JS_Call(
                self.context.as_raw(),
                self.value,
                receiver.value,
                args.len() as i32,
                args.as_slice().as_ptr() as *mut JSValueRaw,
            )
        };

        Self::new(self.context, return_val)
    }

    /// Retrieves the properties of the JavaScript value.
    pub fn properties(&self) -> Result<Properties<'a>> {
        Properties::new(self.context, self.clone())
    }

    /// Retrieves the value of a property with the specified `key` from the JavaScript object.
    pub fn get_property(&self, key: impl Into<Vec<u8>>) -> Result<Self> {
        let cstring_key = CString::new(key)?;
        let raw =
            unsafe { JS_GetPropertyStr(self.context.as_raw(), self.value, cstring_key.as_ptr()) };
        Self::new(self.context, raw)
    }

    /// Sets the value of a property with the specified `key` on the JavaScript object to `val`.
    pub fn set_property(&self, key: impl Into<Vec<u8>>, val: JSValueRef) -> Result<()> {
        // value is being moved into QuickJS, it will be freed there
        let (_, value) = unsafe { val.into_raw() };

        let cstring_key = CString::new(key)?;
        let ret = unsafe {
            JS_DefinePropertyValueStr(
                self.context.as_raw(),
                self.value,
                cstring_key.as_ptr(),
                value,
                JS_PROP_C_W_E as i32,
            )
        };

        if ret < 0 {
            let exception = self.as_exception()?;
            return Err(exception.into_error());
        }
        Ok(())
    }

    /// Retrieves the value of an indexed property from the JavaScript object.
    /// This is used for arrays.
    pub fn get_indexed_property(&self, index: u32) -> Result<Self> {
        let raw = unsafe { JS_GetPropertyUint32(self.context.as_raw(), self.value, index) };
        Self::new(self.context, raw)
    }

    /// Appends a property with the value `val` to the JavaScript object.
    /// This is used for arrays.
    pub fn append_property(&self, val: JSValueRef) -> Result<()> {
        // value is being moved into QuickJS, it will be freed there
        let (_, value) = unsafe { val.into_raw() };

        let len = self.get_property("length")?;
        let ret = unsafe {
            JS_DefinePropertyValueUint32(
                self.context.as_raw(),
                self.value,
                len.value as u32,
                value,
                JS_PROP_C_W_E as i32,
            )
        };

        if ret < 0 {
            let exception = self.as_exception()?;
            return Err(exception.into_error());
        }
        Ok(())
    }

    pub(crate) fn get_tag(&self) -> i32 {
        (self.value >> 32) as i32
    }

    /// All methods in quickjs return an exception value, not an object.
    /// To actually retrieve the exception, we need to retrieve the exception object from the global state.
    fn as_exception(&self) -> Result<Exception> {
        Exception::new(self.context)
    }

    pub fn type_of(&self) -> JSValueType {
        let tag = self.get_tag();
        match tag {
            JS_TAG_INT => JSValueType::Int,
            JS_TAG_BOOL => JSValueType::Bool,
            JS_TAG_NULL => JSValueType::Null,
            JS_TAG_UNDEFINED => JSValueType::Undefined,
            // JS_TAG_FLOAT64 => JSValueType::Float,
            // JS_TAG_BIG_DECIMAL => JSValueType::BigDecimal,
            JS_TAG_BIG_INT => JSValueType::BigInt,
            JS_TAG_BIG_FLOAT => JSValueType::BigFloat,
            JS_TAG_SYMBOL => JSValueType::Symbol,
            JS_TAG_STRING => JSValueType::String,
            JS_TAG_OBJECT
                if unsafe { JS_IsArrayBuffer_Ext(self.context.as_raw(), self.value) == 1 } =>
            {
                JSValueType::ArrayBuffer
            }
            JS_TAG_OBJECT if unsafe { JS_IsArray(self.context.as_raw(), self.value) == 1 } => {
                JSValueType::Array
            }
            JS_TAG_OBJECT if unsafe { JS_IsFunction(self.context.as_raw(), self.value) == 1 } => {
                JSValueType::Function
            }
            JS_TAG_OBJECT => JSValueType::Object,
            JS_TAG_EXCEPTION => JSValueType::Exception,
            t if unsafe { JS_IsFloat64_Ext(t) == 1 } => JSValueType::Float,
            _ => JSValueType::Unknown,
        }
    }
}
impl<'a> Clone for JSValueRef<'a> {
    fn clone(&self) -> Self {
        unsafe {
            Self {
                context: self.context,
                value: JS_DupValue_Ext(self.context.as_raw(), self.value),
            }
        }
    }
}
impl<'a> Drop for JSValueRef<'a> {
    fn drop(&mut self) {
        unsafe { JS_FreeValue_Ext(self.context.as_raw(), self.value) }
    }
}
impl<'a> Debug for JSValueRef<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "JSValueRef({:?}, 0x{:x})[{:?}]",
            self.context,
            self.value,
            self.type_of()
        )?;

        Ok(())
    }
}

// We can't implement From<JSValueRef> for JSValueRaw, as
// JSValueRaw is automatically generated and it would result
// in a cyclic crate dependency.
#[allow(clippy::from_over_into)]
impl Into<JSValueRaw> for JSValueRef<'_> {
    fn into(self) -> JSValueRaw {
        self.value
    }
}

impl fmt::Display for JSValueRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match crate::js_value::qjs_convert::from_qjs_value(self) {
            Ok(v) => write!(f, "{}", v),
            Err(_) => write!(f, "{:?}", self), // TODO: is this better than outright crashing?
        }
    }
}

impl JSValueRef<'_> {
    fn try_to_buffer_ptr(&self) -> Result<(*mut u8, usize)> {
        let mut len: JS_size_t = 0;
        let ptr = unsafe { JS_GetArrayBuffer(self.context.as_raw(), &mut len, self.value) };
        if ptr.is_null() {
            anyhow::bail!("Can't represent {:?} as a buffer", self.value);
        }

        Ok((ptr, len as usize))
    }

    fn try_to_str_wtf8(&self) -> Result<&[u8]> {
        let mut len: JS_size_t = 0;
        // TODO: should we free this string?
        let ptr = unsafe { JS_ToCStringLen2(self.context.as_raw(), &mut len, self.value, 0) }
            as *const u8;

        if ptr.is_null() {
            anyhow::bail!("Can't get string representation of {:?}", self.value);
        }

        Ok(unsafe { std::slice::from_raw_parts(ptr, len as usize) })
    }

    /// Converts the JavaScript value to a string.
    ///
    /// The difference between this method and `TryInto<&str>` implementation is that this method will coerce
    /// values into a string.
    pub fn try_to_str(&self) -> Result<&str> {
        let buffer = self.try_to_str_wtf8()?;
        Ok(str::from_utf8(buffer)?)
    }

    /// Converts the JavaScript value to a string, replacing any invalid UTF-8 sequences with the
    /// Unicode replacement character (U+FFFD).
    pub fn try_to_str_lossy(&self) -> Result<std::borrow::Cow<str>> {
        let mut buffer = self.try_to_str_wtf8()?;
        let res = match str::from_utf8(buffer) {
            Ok(valid) => Cow::Borrowed(valid),
            Err(mut error) => {
                let mut res = String::new();
                loop {
                    let (valid, after_valid) = buffer.split_at(error.valid_up_to());
                    res.push_str(unsafe { str::from_utf8_unchecked(valid) });
                    res.push(char::REPLACEMENT_CHARACTER);

                    // see https://simonsapin.github.io/wtf-8/#surrogate-byte-sequence
                    let lone_surrogate =
                        matches!(after_valid, [0xED, 0xA0..=0xBF, 0x80..=0xBF, ..]);

                    // https://simonsapin.github.io/wtf-8/#converting-wtf-8-utf-8 states that each
                    // 3-byte lone surrogate sequence should be replaced by 1 UTF-8 replacement
                    // char. Rust's `Utf8Error` reports each byte in the lone surrogate byte
                    // sequence as a separate error with an `error_len` of 1. Since we insert a
                    // replacement char for each error, this results in 3 replacement chars being
                    // inserted. So we use an `error_len` of 3 instead of 1 to treat the entire
                    // 3-byte sequence as 1 error instead of as 3 errors and only emit 1
                    // replacement char.
                    let error_len = if lone_surrogate {
                        3
                    } else {
                        error
                            .error_len()
                            .expect("Error length should always be available on underlying buffer")
                    };

                    buffer = &after_valid[error_len..];
                    match str::from_utf8(buffer) {
                        Ok(valid) => {
                            res.push_str(valid);
                            break;
                        }
                        Err(e) => error = e,
                    }
                }
                Cow::Owned(res)
            }
        };

        Ok(res)
    }
}
impl TryFrom<&JSValueRef<'_>> for bool {
    type Error = anyhow::Error;

    fn try_from(value: &JSValueRef) -> Result<Self> {
        match value.type_of() {
            JSValueType::Bool => Ok(value.value as i32 > 0),
            _ => anyhow::bail!("Can't represent {:?} as bool", value.value),
        }
    }
}
impl TryFrom<&JSValueRef<'_>> for i64 {
    type Error = anyhow::Error;

    fn try_from(value: &JSValueRef) -> Result<Self> {
        // There is a JS_ToInt64Ext but that one doesn't report overflow :/
        let mut int = 0_i64;

        let err = match value.type_of() {
            JSValueType::BigInt => unsafe {
                JS_BigIntToInt64(value.context.as_raw(), &mut int, value.value)
            },
            JSValueType::Float | JSValueType::BigFloat => {
                /// Maximum safe range of i64 expressed as f64.
                const MAX_SAFE_RANGE_FLOAT: RangeInclusive<f64> = i64::MIN as f64..=i64::MAX as f64;

                let float = f64::try_from(value)?;
                if float.fract() == 0.0 && MAX_SAFE_RANGE_FLOAT.contains(&float) {
                    int = float as i64;
                    0
                } else {
                    // infinite, NaN, has fractional part or doesn't fit into an integer
                    -1
                }
            }
            _ => unsafe {
                // this function can coerce:
                // Int
                // Bool
                // Null
                // Undefined
                // Float
                // BigFloat
                //
                // unfortunately float overflows aren't reported
                JS_ToInt64(value.context.as_raw(), &mut int, value.value)
            },
        };

        if err != 0 {
            anyhow::bail!("Value is not a number or does not fit into i64")
        }

        Ok(int)
    }
}
impl TryFrom<&JSValueRef<'_>> for u64 {
    type Error = anyhow::Error;

    fn try_from(value: &JSValueRef) -> Result<Self> {
        let uint = match value.type_of() {
            JSValueType::BigInt => {
                let mut uint = 0u64;
                let err =
                    unsafe { JS_BigIntToUint64(value.context.as_raw(), &mut uint, value.value) };
                if err != 0 {
                    anyhow::bail!("Value is not a number or does not fit into u64")
                }

                uint
            }
            JSValueType::Float | JSValueType::BigFloat => {
                /// Maximum safe range of u64 expressed as f64.
                const MAX_SAFE_RANGE_FLOAT: RangeInclusive<f64> = u64::MIN as f64..=u64::MAX as f64;

                let float = f64::try_from(value)?;
                if float.fract() == 0.0 && MAX_SAFE_RANGE_FLOAT.contains(&float) {
                    float as u64
                } else {
                    anyhow::bail!("Value does not fit into u64")
                }
            }
            _ => u64::try_from(i64::try_from(value)?)?,
        };

        Ok(uint)
    }
}
impl TryFrom<&JSValueRef<'_>> for f64 {
    type Error = anyhow::Error;

    fn try_from(value: &JSValueRef) -> Result<Self> {
        let mut float = 0f64;

        // this handles:
        // Int
        // Bool
        // Null
        // Float
        // BigInt
        // BigFloat
        // TODO: and aborts for others??
        let err = unsafe { JS_ToFloat64(value.context.as_raw(), &mut float, value.value) };
        if err != 0 {
            anyhow::bail!("Value is not a number");
        }

        Ok(float)
    }
}
impl<'a> TryFrom<&'a JSValueRef<'_>> for &'a [u8] {
    type Error = anyhow::Error;

    fn try_from(value: &'a JSValueRef) -> Result<Self> {
        let (ptr, len) = value.try_to_buffer_ptr()?;

        Ok(unsafe { std::slice::from_raw_parts(ptr, len) })
    }
}
impl<'a> TryFrom<&'a JSValueRef<'_>> for &'a mut [u8] {
    type Error = anyhow::Error;

    fn try_from(value: &'a JSValueRef) -> Result<Self> {
        let (ptr, len) = value.try_to_buffer_ptr()?;

        Ok(unsafe { std::slice::from_raw_parts_mut(ptr, len) })
    }
}
impl<'a> TryFrom<&'a JSValueRef<'_>> for &'a str {
    type Error = anyhow::Error;

    fn try_from(value: &'a JSValueRef) -> Result<Self> {
        match value.type_of() {
            JSValueType::String => value.try_to_str(),
            _ => anyhow::bail!("Value must be a string"),
        }
    }
}
impl TryFrom<&JSValueRef<'_>> for usize {
    type Error = anyhow::Error;

    fn try_from(value: &JSValueRef) -> Result<Self> {
        let uint = u64::try_from(value)?;
        Ok(usize::try_from(uint)?)
    }
}

#[cfg(test)]
mod tests {
    use super::JSValueType;

    use crate::js_binding::constants::MAX_SAFE_INTEGER;
    use crate::js_binding::constants::MIN_SAFE_INTEGER;

    use super::JSContextRef;
    use anyhow::Result;
    const SCRIPT_NAME: &str = "value.js";

    #[test]
    fn test_value_objects_allow_retrieving_a_str_property() -> Result<()> {
        let ctx = JSContextRef::default();
        let contents = "globalThis.bar = 1;";
        let _ = ctx.eval_global(SCRIPT_NAME, contents)?;
        let global = ctx.global_object()?;
        let prop = global.get_property("bar");
        assert!(prop.is_ok());
        Ok(())
    }

    #[test]
    fn test_value_objects_allow_setting_a_str_property() -> Result<()> {
        let ctx = JSContextRef::default();
        let obj = ctx.object_value()?;
        obj.set_property("foo", ctx.value_from_i32(1_i32)?)?;
        let val = obj.get_property("foo");
        assert!(val.is_ok());
        assert_eq!(val.unwrap().type_of(), JSValueType::Int);
        Ok(())
    }

    #[test]
    fn test_value_objects_allow_setting_an_indexed_property() {
        let ctx = JSContextRef::default();
        let seq = ctx.array_value().unwrap();
        seq.append_property(ctx.value_from_str("hello").unwrap())
            .unwrap();
        seq.append_property(ctx.value_from_str("world").unwrap())
            .unwrap();

        let val = seq.get_indexed_property(0).unwrap();
        assert_eq!(<&str>::try_from(&val).unwrap(), "hello");

        let val = seq.get_indexed_property(1).unwrap();
        assert_eq!(<&str>::try_from(&val).unwrap(), "world");
    }

    #[test]
    fn test_value_set_property_returns_exception() {
        let ctx = JSContextRef::default();
        let val = ctx.value_from_i32(1337).unwrap();
        let err = val
            .set_property("foo", ctx.value_from_str("hello").unwrap())
            .unwrap_err();
        assert_eq!(
            "Uncaught TypeError: not an object\n".to_string(),
            err.to_string()
        );
    }

    #[test]
    fn test_value_append_property_returns_exception() {
        let ctx = JSContextRef::default();
        let val = ctx.value_from_i32(1337).unwrap();
        let err = val
            .append_property(ctx.value_from_str("hello").unwrap())
            .unwrap_err();
        assert_eq!(
            "Uncaught TypeError: not an object\n".to_string(),
            err.to_string()
        );
    }

    #[test]
    fn test_value_objects_allow_retrieving_a_indexed_property() -> Result<()> {
        let ctx = JSContextRef::default();
        let contents = "globalThis.arr = [1];";
        let _ = ctx.eval_global(SCRIPT_NAME, contents)?;
        let val = ctx
            .global_object()?
            .get_property("arr")?
            .get_indexed_property(0);
        assert!(val.is_ok());
        assert_eq!(val.unwrap().type_of(), JSValueType::Int);
        Ok(())
    }

    #[test]
    fn test_allows_representing_a_value_as_f64() -> Result<()> {
        let ctx = JSContextRef::default();
        let val = f64::try_from(&ctx.value_from_f64(f64::MIN)?).unwrap();
        assert_eq!(val, f64::MIN);
        Ok(())
    }

    #[test]
    fn test_value_as_str() {
        let s = "hello";
        let ctx = JSContextRef::default();
        let val = ctx.value_from_str(s).unwrap();
        assert_eq!(<&str>::try_from(&val).unwrap(), s);
    }

    #[test]
    fn test_value_as_str_middle_nul_terminator() {
        let s = "hello\0world!";
        let ctx = JSContextRef::default();
        let val = ctx.value_from_str(s).unwrap();
        assert_eq!(<&str>::try_from(&val).unwrap(), s);
    }

    #[test]
    fn test_exception() {
        let ctx = JSContextRef::default();
        let error = ctx
            .eval_global("main", "should_throw")
            .unwrap_err()
            .to_string();
        let expected_error =
            "Uncaught ReferenceError: \'should_throw\' is not defined\n    at <eval> (main)\n";
        assert_eq!(expected_error, error.as_str());
    }

    #[test]
    fn test_exception_with_stack() {
        let ctx = JSContextRef::default();
        let script = r#"
            function foo() { return bar(); }
            function bar() { return foobar(); }
            function foobar() {
                for (var i = 0; i < 100; i++) {
                    if (i > 25) {
                        throw new Error("boom");
                    }
                }
            }
            foo();
        "#;
        let expected_error = r#"Uncaught Error: boom
    at foobar (main:7)
    at bar (main)
    at foo (main)
    at <eval> (main:11)
"#;
        let error = ctx.eval_global("main", script).unwrap_err().to_string();
        assert_eq!(expected_error, error.as_str());
    }

    #[test]
    fn test_syntax_error() {
        let ctx = JSContextRef::default();
        let error = ctx
            .eval_global("main", "func boom() {}")
            .unwrap_err()
            .to_string();
        let expected_error = "Uncaught SyntaxError: expecting \';\'\n    at main:1\n";
        assert_eq!(expected_error, error.as_str());
    }

    #[test]
    fn test_is_null_or_undefined() {
        let ctx = JSContextRef::default();
        let v = ctx.undefined_value().unwrap();
        assert!(v.type_of().is_null_or_undefined());

        let v = ctx.null_value().unwrap();
        assert!(v.type_of().is_null_or_undefined());

        let v = ctx.value_from_i32(1337).unwrap();
        assert!(!v.type_of().is_null_or_undefined());
    }

    #[test]
    fn test_i64() {
        let ctx = JSContextRef::default();

        // max
        let val = i64::MAX;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // min
        let val = i64::MIN;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // zero
        let val = 0;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::Int);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // MAX_SAFE_INTEGER
        let val = MAX_SAFE_INTEGER;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::Float);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // MAX_SAFE_INTGER + 1
        let val = MAX_SAFE_INTEGER + 1;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // MIN_SAFE_INTEGER
        let val = MIN_SAFE_INTEGER;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::Float);
        assert_eq!(i64::try_from(&v).unwrap(), val);

        // MIN_SAFE_INTEGER - 1
        let val = MIN_SAFE_INTEGER - 1;
        let v = ctx.value_from_i64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(i64::try_from(&v).unwrap(), val);
    }

    #[test]
    fn test_u64() {
        let ctx = JSContextRef::default();

        // max
        let val = u64::MAX;
        let v = ctx.value_from_u64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(u64::try_from(&v).unwrap(), val);

        // min == 0
        let val = u64::MIN;
        let v = ctx.value_from_u64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::Int);
        assert_eq!(i64::try_from(&v).unwrap() as u64, val);

        // MAX_SAFE_INTEGER
        let val = MAX_SAFE_INTEGER as u64;
        let v = ctx.value_from_u64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::Float);
        assert_eq!(i64::try_from(&v).unwrap() as u64, val);

        // MAX_SAFE_INTEGER + 1
        let val = MAX_SAFE_INTEGER as u64 + 1;
        let v = ctx.value_from_u64(val).unwrap();
        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(u64::try_from(&v).unwrap(), val);
    }

    #[test]
    fn test_value_larger_than_u64_max_returns_overflow_error() {
        let ctx = JSContextRef::default();

        ctx.eval_global("main", "var num = BigInt(\"18446744073709551616\");")
            .unwrap(); // u64::MAX + 1
        let num = ctx.global_object().unwrap().get_property("num").unwrap();

        assert_eq!(num.type_of(), JSValueType::BigInt);
        assert_eq!(
            u64::try_from(&num).unwrap_err().to_string(),
            "Value is not a number or does not fit into u64"
        );
    }

    #[test]
    fn test_value_smaller_than_i64_min_returns_underflow_error() {
        let ctx = JSContextRef::default();

        ctx.eval_global("main", "var num = BigInt(\"-9223372036854775809\");")
            .unwrap(); // i64::MIN - 1
        let num = ctx.global_object().unwrap().get_property("num").unwrap();

        assert_eq!(num.type_of(), JSValueType::BigInt);
        assert_eq!(
            i64::try_from(&num).unwrap_err().to_string(),
            "Value is not a number or does not fit into i64"
        );
    }

    #[test]
    fn test_u64_creates_an_unsigned_bigint() {
        let ctx = JSContextRef::default();

        let val = i64::MAX as u64 + 2;
        let v = ctx.value_from_u64(val).unwrap();

        assert_eq!(v.type_of(), JSValueType::BigInt);
        assert_eq!(u64::try_from(&v).unwrap(), val);
    }

    #[test]
    fn test_is_function() {
        let ctx = JSContextRef::default();

        ctx.eval_global("main", "var x = 42; function foo() {}")
            .unwrap();

        assert_ne!(
            ctx.global_object()
                .unwrap()
                .get_property("x")
                .unwrap()
                .type_of(),
            JSValueType::Function
        );

        assert_eq!(
            ctx.global_object()
                .unwrap()
                .get_property("foo")
                .unwrap()
                .type_of(),
            JSValueType::Function
        );
    }

    #[test]
    fn test_eval_function() {
        let ctx = JSContextRef::default();

        let bytecode = ctx.compile_global("main", "var f = 42;").unwrap();
        ctx.value_from_bytecode(&bytecode)
            .unwrap()
            .eval_function()
            .unwrap();

        assert_eq!(
            i64::try_from(&ctx.global_object().unwrap().get_property("f").unwrap()).unwrap(),
            42
        );
    }

    #[test]
    fn test_convert_bool() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "true")?;

        assert_eq!(val.to_string(), "true");

        let val_ref = &val;
        let arg: bool = val_ref.try_into()?;
        assert!(arg);

        Ok(())
    }

    #[test]
    fn test_convert_i64() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "42")?;

        assert_eq!(val.to_string(), "42");

        let val_ref = &val;
        let arg: i64 = val_ref.try_into()?;
        assert_eq!(arg, 42);

        Ok(())
    }

    #[test]
    fn test_convert_u64() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "42")?;

        assert_eq!(val.to_string(), "42");

        let val_ref = &val;
        let arg: u64 = val_ref.try_into()?;
        assert_eq!(arg, 42);

        Ok(())
    }

    #[test]
    fn test_convert_f64() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "42.42")?;

        assert_eq!(val.to_string(), "42.42");

        let val_ref = &val;
        let arg: f64 = val_ref.try_into()?;
        assert_eq!(arg, 42.42);

        Ok(())
    }

    #[test]
    fn test_convert_str() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "const h = 'hello'; h")?;

        assert_eq!(val.to_string(), "hello");

        let val_ref = &val;
        let arg: &str = val_ref.try_into()?;
        assert_eq!(arg, "hello");

        Ok(())
    }

    #[test]
    fn test_convert_bytes() -> Result<()> {
        let context = JSContextRef::default();
        let val = context.eval_global("test.js", "new ArrayBuffer(8)")?;

        let expected = [0_u8; 8].to_vec();

        assert_eq!(val.to_string(), "[object ArrayBuffer]");

        let val_ref = &val;
        let arg: &[u8] = val_ref.try_into()?;
        assert_eq!(arg, expected);

        Ok(())
    }
}
