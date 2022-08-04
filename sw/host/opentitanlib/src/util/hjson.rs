use std::any::{type_name, Any};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::marker::PhantomData;

use anyhow::{anyhow, Result};

use serde::de;
use serde::{Deserialize, Deserializer};

use crate::util::parse_int::ParseInt;

/// Trait for handling HJSON deserialization with support for post-processing.
///
/// This trait is intended to be derived by using the `#[derive(HjsonCompoundDeser)]` proc macro
/// provided by `opentitantool_derive`. Once derived, the associated struct can be deserialized in
/// the same way as calling `deser_hjson::from_str()` with an additional `backend` argument. The
/// `backend` argument can be used to process special values encountered during deserilization. For
/// regular HJSON deserialization either use the `deser_hjson` crate directly or pass `&mut
/// Default::default()` as the `backend`.
pub trait HjsonCompoundDeser: Clone {
    fn from_str(s: &str, backend: &mut DeserBackend) -> Result<Self>
    where
        Self: Sized;
}

/// Additional state used in the backend of `HjsonCompoundDeser::from_str()`.
#[derive(Default)]
pub struct DeserBackend {
    // TODO(jflat) Add symbol_map support
    _symbol_map: HashMap<String, Box<dyn Any>>,
}

/// Meta information provided by the serde deserilization step.
enum HjsonFieldType<V> {
    Value(V),
    Identifier(String),
    Nested(Box<dyn HjsonUnpack<V>>),
}

/// Wrapper for fields within structs that implement `HjsonCompoundDeser`.
///
/// As part of deriving `HjsonCompoundDeser` a companion struct is generated that wraps all fields
/// as `HjsonFields`. This allows for passing additional information to the serde deserializer,
/// like the format of string wrapped integer constants, as well as deferring value resolution to
/// the `DeserBacked` in situations where a field's value cannot be determined by serde.
struct HjsonField<V, F: HjsonFormatter<V>> {
    val: HjsonFieldType<V>,
    formatter: PhantomData<F>,
}

trait HjsonUnpack<V> {
    fn unpack_value(&self, _symbols: &mut DeserBackend) -> Result<V>;
}

impl<V, F> HjsonUnpack<V> for HjsonField<V, F>
where
    F: HjsonFormatter<V>,
    V: Clone,
{
    fn unpack_value(&self, backend: &mut DeserBackend) -> Result<V> {
        match &self.val {
            HjsonFieldType::Value(v) => Ok(v.clone()),
            HjsonFieldType::Identifier(ident) => {
                unimplemented!("Cannot unpack {}", ident);
            }
            HjsonFieldType::Nested(v) => v.unpack_value(backend),
        }
    }
}

/// Implements `Deserailize` for a particular `HjsonField<V, _>`.
///
/// Deserializing values as `HjsonField`s is a bit of a pain. We cannot tell the `Visitor` which
/// type to visit in advance since any value can hide inside a string. Blanket implementations for
/// `visit_*()` don't work either, since `deserialize_any()` can dispatch to different visit
/// functions depending on what the deserializer encounters. For instance, if we are deserializing a
/// field `foo: f32`, we need to implement `visit_u64()`, `visit_i64()`, `visit_f64()`, and
/// `visit_str()` to return a `HjsonFieldType::Value(f32)`, as any of those functions could be
/// called by the deserializer. The solution is to implement a `Deserialize` independently for each
/// type we want to be able to wrap in `HjsonField`.
///
/// A call to `deser_impl!(i64, (visit_u64, u64), (visit_i64, i64))` will expand into
/// ```
///
/// impl<'de, F: HjsonFormatter<u64>> Deserialize<'de> for HjsonField<u64, F> {
///     fn deserialize<D>(deserializer: D) -> Result<HjsonField<u64, F>, D::Error>
///         where
///     D: Deserializer<'de>,
///     {
///         struct Visitor<F>(PhantomData<F>);
///         impl<'a, F: HjsonFormatter<u64>> de::Visitor<'a> for Visitor<F> {
///             type Value = HjsonFieldType<u64>;
///
///             fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
///                 formatter.write_fmt(format_args!("a value parsable to {}", type_name::<$ty_to>()))
///             }
///
///             fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
///             where
///                 E: de::Error,
///             {
///                 (|v: u64| visit_default(v, PhantomData::<F>::defualt()))(value)
///             }
///
///             fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E>
///             where
///                 E: de::Error,
///             {
///                 (|v: i64| visit_default(v, PhantomData::<F>::defualt()))(value)
///             }
///
///             fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
///             where
///                 E: de::Error,
///             {
///                 (|v: &str| visit_wrapped(v, PhantomData::<F>::defualt()))(value)
///             }
///
///         }
///         Ok(HjsonField::<$ty_to, F> {
///             val: deserializer.deserialize_any(Visitor {
///                 0: PhantomData::<F>,
///             })?,
///             formatter: Default::default(),
///         })
///     }
/// }
/// ```
macro_rules! deser_impl {
    // Generate a `Deserialize` impl block that deserializes into `HjsonField<$ty_to, F>` by
    // calling one of the provided visit functions.
    ($ty_to: ty, $(($visit_funcs:ident, $ty_froms:ty, $bodies:expr)),+) => {
        deser_custom_impl!(
            $ty_to,
            $(($visit_funcs, $ty_froms, $bodies)),+,
            (visit_str, &str, |v: &str| visit_wrapped(v, PhantomData::<F>::default())));
    };
    ($ty_to: ty, $(($visit_funcs:ident, $ty_froms:ty)),+) => {
        deser_custom_impl!(
            $ty_to,
            $(($visit_funcs, $ty_froms, |v: $ty_froms| visit_default(v, PhantomData::<$ty_to>::default()))),+,
            (visit_str, &str, |v: &str| visit_wrapped(v, PhantomData::<F>::default())));
    };
}

macro_rules! deser_custom_impl {
    ($ty_to: ty, $(($visit_funcs:ident, $ty_froms:ty, $bodies:expr)),+) => {
        impl<'de, F: HjsonFormatter<$ty_to>> Deserialize<'de> for HjsonField<$ty_to, F> {
            fn deserialize<D>(deserializer: D) -> Result<HjsonField<$ty_to, F>, D::Error>
                where
            D: Deserializer<'de>,
            {
                struct Visitor<F>(PhantomData<F>);
                impl<'a, F: HjsonFormatter<$ty_to>> de::Visitor<'a> for Visitor<F> {
                    type Value = HjsonFieldType<$ty_to>;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_fmt(format_args!("a value parsable to {}", type_name::<$ty_to>()))
                    }

                    $(expand_visit_func!($visit_funcs, $ty_froms, $bodies);)+

                }
                Ok(HjsonField::<$ty_to, F> {
                    val: deserializer.deserialize_any(Visitor {
                        0: PhantomData::<F>,
                    })?,
                    formatter: Default::default(),
                })
            }
        }
    };
}

macro_rules! expand_visit_func {
    ($visit_func:ident, $ty_from:ty, $body:expr) => {
        fn $visit_func<E>(self, value: $ty_from) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            $body(value)
        }
    };
}

// Takes a `value` of type `V`, attempts to convert it to type `R`, and wraps it as an
// `HjsonFieldType::Value(R)`.
fn visit_default<V, R, E>(value: V, _output: PhantomData<R>) -> Result<HjsonFieldType<R>, E>
where
    E: de::Error,
    R: TryFrom<V>,
    V: std::fmt::Display + Copy,
{
    Ok(HjsonFieldType::Value(value.try_into().map_err(|_| {
        de::Error::custom(format_args!(
            "got {} \"{}\", expected a value that converts to type {}",
            type_name::<V>(),
            value,
            type_name::<R>()
        ))
    })?))
}

// Invokes the provided formatter on `value`. If the formatter fails the provided str is treated as
// an identifier for the backend to handle.
fn visit_wrapped<E, V, F>(value: &str, _formatter: PhantomData<F>) -> Result<HjsonFieldType<V>, E>
where
    E: de::Error,
    F: HjsonFormatter<V>,
{
    Ok(match F::hjson_format(value) {
        Ok(val) => HjsonFieldType::Value(val),
        Err(_) => HjsonFieldType::Identifier(value.to_owned()),
    })
}

deser_impl!(u64, (visit_u64, u64));
deser_impl!(u32, (visit_u64, u64));
deser_impl!(u16, (visit_u64, u64));
deser_impl!(u8, (visit_u64, u64));
deser_impl!(usize, (visit_u64, u64));

deser_impl!(i64, (visit_u64, u64), (visit_i64, i64));
deser_impl!(i32, (visit_u64, u64), (visit_i64, i64));
deser_impl!(i16, (visit_u64, u64), (visit_i64, i64));
deser_impl!(i8, (visit_u64, u64), (visit_i64, i64));
deser_impl!(isize, (visit_u64, u64), (visit_i64, i64));

deser_impl!(bool, (visit_bool, bool));

fn f64_downcast_err<V, E>(val: V) -> E
where
    V: std::fmt::Display,
    E: de::Error,
{
    de::Error::custom(format_args!("could not downcast {} to f64", val))
}

fn f32_downcast_err<V, E>(val: V) -> E
where
    V: std::fmt::Display,
    E: de::Error,
{
    de::Error::custom(format_args!("could not downcast {} to f32", val))
}

deser_impl!(
    f64,
    (visit_u64, u64, |val: u64| {
        Ok(HjsonFieldType::Value(
            u32::try_from(val)
                .map_err(|_| f64_downcast_err(val))?
                .into(),
        ))
    }),
    (visit_i64, i64, |val: i64| {
        Ok(HjsonFieldType::Value(
            i32::try_from(val)
                .map_err(|_| f64_downcast_err(val))?
                .into(),
        ))
    }),
    (visit_f64, f64, |val: f64| Ok(HjsonFieldType::Value(val)))
);
deser_impl!(
    f32,
    (visit_u64, u64, |val: u64| {
        Ok(HjsonFieldType::Value(
            u16::try_from(val)
                .map_err(|_| f32_downcast_err(val))?
                .into(),
        ))
    }),
    (visit_i64, i64, |val: i64| {
        Ok(HjsonFieldType::Value(
            i16::try_from(val)
                .map_err(|_| f32_downcast_err(val))?
                .into(),
        ))
    }),
    (visit_f64, f64, |val: f64| Ok(HjsonFieldType::Value(
        val as f32
    )))
);

deser_custom_impl!(
    String,
    (visit_string, String, |val| Ok(HjsonFieldType::Value(val)))
);

/// Trait for describing how a string wrapped value should be parsed.
pub trait HjsonFormatter<T> {
    fn hjson_format(content: &str) -> Result<T>;
}

/// Describes a field as representing a decimal literal.
pub struct DecimalFormat;
/// Describes a field as representing a hexadecimal literal.
pub struct HexFormat;
/// Describes a field as representing a octal literal.
pub struct OctFormat;
/// Describes a field that should be parsed based on context.
///
/// For instance:
///   "12" => Decimal
///   "0x34" => Hexadecimal
///   "056" => Octal
///
/// This behavior is the same as `ParseInt::from_str()`.
pub struct FromContext;

impl<T: ParseInt> HjsonFormatter<T> for DecimalFormat {
    fn hjson_format(content: &str) -> Result<T> {
        T::from_str_radix(content, 10).map_err(|e| anyhow!(e))
    }
}

impl<T: ParseInt> HjsonFormatter<T> for HexFormat {
    fn hjson_format(content: &str) -> Result<T> {
        T::from_str_radix(content, 16).map_err(|e| anyhow!(e))
    }
}

impl<T: ParseInt> HjsonFormatter<T> for OctFormat {
    fn hjson_format(content: &str) -> Result<T> {
        T::from_str_radix(content, 8).map_err(|e| anyhow!(e))
    }
}

impl<T: ParseInt> HjsonFormatter<T> for FromContext {
    fn hjson_format(content: &str) -> Result<T> {
        T::from_str(content).map_err(|e| anyhow!(e))
    }
}

impl HjsonFormatter<String> for FromContext {
    fn hjson_format(content: &str) -> Result<String> {
        Ok(content.to_owned())
    }
}

macro_rules! unparsable_from_context {
    ($ty:ident) => {
        impl HjsonFormatter<$ty> for FromContext {
            fn hjson_format(_content: &str) -> Result<$ty> {
                Err(anyhow!(concat!(
                    "Cannot parse {} from context",
                    stringify!($ty)
                )))
            }
        }
    };
}

unparsable_from_context!(f32);
unparsable_from_context!(f64);
unparsable_from_context!(char);
unparsable_from_context!(bool);

#[cfg(test)]
mod test {
    use super::*;
    use opentitantool_derive::HjsonCompoundDeser;

    #[test]
    fn test_hjson_derive() {
        #[derive(HjsonCompoundDeser, Clone)]
        struct TestStruct {
            _foo: u32,
            #[format("DecimalFormat")]
            _bar: u32,
        }
    }

    #[test]
    fn test_hjson_format() {
        #[derive(HjsonCompoundDeser, Clone)]
        struct TestStruct {
            context: u32,
            #[format("DecimalFormat")]
            decimal: u32,
            #[format("HexFormat")]
            hex: u32,
            #[format("OctFormat")]
            octal: u32,
        }

        let hjson = stringify!(
        {
            context: "0xa5",
            decimal: "0123",
            hex: "0456",
            octal: "123",
        }
        );

        let result = TestStruct::from_str(&hjson, &mut Default::default()).unwrap();
        assert_eq!(result.context, 0xa5);
        assert_eq!(result.decimal, 123);
        assert_eq!(result.hex, 0x456);
        assert_eq!(result.octal, 0o123);
    }

    #[test]
    fn test_hjson_diverse_fields() {
        #[derive(HjsonCompoundDeser, Clone, PartialEq, Debug)]
        struct TestStruct {
            val_bool: bool,
            val_usize: usize,
            val_isize: isize,
            val_isize_neg: isize,
            val_u8: u8,
            val_i8: i8,
            val_i8_neg: i8,
            val_u16: u16,
            val_i16: i16,
            val_i16_neg: i16,
            val_u32: u32,
            val_i32: i32,
            val_i32_neg: i32,
            val_u64: u64,
            val_i64: i64,
            val_i64_neg: i64,
            val_f32: f32,
            val_f32_from_uint: f32,
            val_f32_from_int: f32,
            val_f64: f64,
            val_f64_from_uint: f64,
            val_f64_from_int: f64,
            val_wrapped_u32: u32,
            val_string: String,
        }

        let hjson = r#"
        {
            val_bool: true,
            val_usize: 42,
            val_isize: 42,
            val_isize_neg: -42,
            val_u8: 42,
            val_i8: 42,
            val_i8_neg: -42,
            val_u16: 42,
            val_i16: 42,
            val_i16_neg: -42,
            val_u32: 42,
            val_i32: 42,
            val_i32_neg: -42,
            val_u64: 42,
            val_i64: 42,
            val_i64_neg: -42,
            val_f32: 42.0,
            val_f32_from_uint: 42,
            val_f32_from_int: -42,
            val_f64: 42.0,
            val_f64_from_uint: 42,
            val_f64_from_int: -42,
            val_wrapped_u32: "42",
            val_string: "42",
        }"#;
        let expected = TestStruct {
            val_bool: true,
            val_usize: 42,
            val_isize: 42,
            val_isize_neg: -42,
            val_u8: 42,
            val_i8: 42,
            val_i8_neg: -42,
            val_u16: 42,
            val_i16: 42,
            val_i16_neg: -42,
            val_u32: 42,
            val_i32: 42,
            val_i32_neg: -42,
            val_u64: 42,
            val_i64: 42,
            val_i64_neg: -42,
            val_f32: 42.0,
            val_f32_from_uint: 42.0,
            val_f32_from_int: -42.0,
            val_f64: 42.0,
            val_f64_from_uint: 42.0,
            val_f64_from_int: -42.0,
            val_wrapped_u32: 42,
            val_string: "42".to_owned(),
        };
        let result = TestStruct::from_str(&hjson, &mut Default::default()).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_hjson_nested() {
        #[derive(HjsonCompoundDeser, Clone, PartialEq, Debug)]
        struct TestStructInner {
            val_u32: u32,
        }
        #[derive(HjsonCompoundDeser, Clone, PartialEq, Debug)]
        struct TestStructOutter {
            #[nested]
            inner: TestStructInner,
        }

        let hjson = r#"
        {
            inner: {
                val_u32: 42
            }
        }
        "#;
        let expected = TestStructOutter {
            inner: TestStructInner { val_u32: 42 },
        };
        let result = TestStructOutter::from_str(&hjson, &mut Default::default()).unwrap();
        assert_eq!(result, expected);
    }
}
