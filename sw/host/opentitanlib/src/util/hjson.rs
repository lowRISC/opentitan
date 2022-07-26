use std::marker::PhantomData;
use std::ops::FnMut;
use std::collections::HashMap;
use std::any::{Any, type_name};
use std::fmt;

use anyhow::Result;

use serde::{Deserialize, Deserializer, de};

pub struct DeserBackend {
    symbol_map: HashMap<String, Box<dyn Any>>,
}

pub enum HjsonFieldType<V> {
    Value(V),
    Identifier(String),
}

pub struct HjsonField<V, F: HjsonFormatter<V>> {
    val: HjsonFieldType<V>,
    formatter: PhantomData<F>,
}

impl<V, F> HjsonField<V, F> where F: HjsonFormatter<V> {
    fn unpack_value(self, symbols: &mut DeserBackend) -> Result<V> {
        match self.val {
            HjsonFieldType::Value(v) => Ok(v),
            HjsonFieldType::Identifier(_ident) => {
                unimplemented!();
            }
        }
    }
}

impl<'de, V, F> Deserialize<'de> for HjsonField<V, F>
        where F: HjsonFormatter<V>, V: Deserialize<'de> {
    fn deserialize<D>(deserializer: D) -> Result<HjsonField<V, F>, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct Visitor<V, F>(PhantomData<V>, PhantomData<F>);

        impl<'a, V, F: HjsonFormatter<V>> de::Visitor<'a> for Visitor<V, F> {
            type Value = HjsonFieldType::<V>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_fmt(format_args!("a value parsable to {}", type_name::<V>()))
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(HjsonFieldType::Value(F::hjson_format(value).unwrap()))
            }
        }
        Ok(HjsonField::<V,F> {
            val: deserializer.deserialize_any(Visitor {
                0: PhantomData::<V>,
                1: PhantomData::<F>,
            })?,
            formatter: Default::default(),
        })
    }
}

pub trait HjsonFormatter<T> {
    fn hjson_format(content: &str) -> Result<T>;
}

pub trait HjsonCompoundDeser {
    fn from_str(s: &str, backend: &mut DeserBackend) -> Result<Self> where Self: Sized;
}

pub struct DecimalFormat;
pub struct FromContext;

impl HjsonFormatter<u32> for DecimalFormat {
    fn hjson_format(content: &str) -> Result<u32> {
        Ok(456)
    }
}

impl HjsonFormatter<u32> for FromContext {
    fn hjson_format(content: &str) -> Result<u32> {
        Ok(123)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use opentitantool_derive::HjsonCompoundDeser;

    #[test]
    fn test_derive() {
        #[derive(HjsonCompoundDeser)]
        struct TestStruct {
            foo: u32,
            #[format("DecimalFormat")]
            bar: u32,
        }
    }

    #[test]
    fn test_deserialzie() {
        #[derive(HjsonCompoundDeser)]
        struct TestStruct {
            foo: u32,
            #[format("DecimalFormat")]
            bar: u32,
        }

        let hjson = stringify!(
        {
            foo: "123",
            bar: "456",
        }
        );

        let mut backend = DeserBackend {
            symbol_map: Default::default(),
        };

        let result = TestStruct::from_str(&hjson, &mut backend).unwrap();
        assert_eq!(result.foo, 123);
        assert_eq!(result.bar, 456);
    }
}
