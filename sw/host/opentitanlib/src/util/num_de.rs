// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/// Deserialization utilities for certain values in OTP HJSON files.
///
/// The OTP HJSON files have some strange values:
///
/// Integers, sometimes wrapped in strings, with inconsistent formatting and meta values, such as:
///   - value: "0x739"
///   - key_size: "16"
///   - seed: "10556718629619452145"
///   - seed: 01931961561863975174  // This is a decimal integer, not octal.
///   - value: "<random>"
///
/// Additionally, some values have sizes defined within the config files themselves, such as the
/// keys. This module exists to handle these peculiar cases.
use anyhow::Result;
use rand::RngCore;
use serde::de::{self, Deserializer, Unexpected};
use serde::ser::Serializer;
use serde::{Deserialize, Serialize};
use std::any::type_name;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

use crate::util::parse_int::{ParseInt, ParseIntError};

/// Deserialize numeric types from HJSON config files.
pub fn deserialize<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: ParseInt,
{
    struct Visitor<U>(PhantomData<U>);

    impl<'a, U: ParseInt> de::Visitor<'a> for Visitor<U> {
        type Value = U;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_fmt(format_args!("a string that parses to {}", type_name::<U>()))
        }

        fn visit_string<E>(self, mut name: String) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            if name.starts_with("false") {
                name = "0".to_owned()
            } else if name.starts_with("true") {
                name = "1".to_owned()
            }

            let trimmed = if name.starts_with("0x") {
                &name
            } else {
                let trimmed = name[0..name.len() - 1].trim_start_matches('0');
                &name[name.len() - trimmed.len() - 1..]
            };

            match U::from_str(trimmed) {
                Ok(value) => Ok(value),
                Err(_) => Err(de::Error::invalid_value(Unexpected::Str(trimmed), &self)),
            }
        }

        fn visit_str<E>(self, name: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            self.visit_string(name.to_owned())
        }

        fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            if v {
                self.visit_str("1")
            } else {
                self.visit_str("0")
            }
        }
    }

    deserializer.deserialize_string(Visitor(PhantomData::<T>))
}

/// Placeholder type for values that cannot be resolved during deserialization.
#[derive(Debug, PartialEq, Clone)]
enum DeferredInit {
    Initialized(Vec<u8>),
    Random,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DeferredValue(#[serde(deserialize_with = "deserialize")] DeferredInit);

impl DeferredValue {
    pub fn resolve(&self, size: usize, rng: &mut dyn RngCore) -> Vec<u8> {
        match self.0.clone() {
            DeferredInit::Initialized(mut vec) => {
                vec.resize(size, 0);
                vec
            }
            DeferredInit::Random => {
                let mut vec = vec![0u8; size];
                rng.fill_bytes(&mut vec);
                vec
            }
        }
    }

    pub fn is_initialized(&self) -> bool {
        matches!(self.0, DeferredInit::Initialized(_))
    }
}

impl ParseInt for DeferredInit {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        Ok(DeferredInit::Initialized(Vec::<u8>::from_str_radix(
            src, radix,
        )?))
    }

    fn from_str(src: &str) -> Result<Self, ParseIntError> {
        if src == "<random>" {
            Ok(DeferredInit::Random)
        } else {
            Ok(DeferredInit::Initialized(Vec::<u8>::from_str(src)?))
        }
    }
}

impl Deref for DeferredValue {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match &self.0 {
            DeferredInit::Initialized(val) => val,
            _ => panic!("Value has not been initialized"),
        }
    }
}

/// Wrapper type to force deserialization assuming octal encoding.
#[derive(Clone, Deserialize, Debug, PartialEq)]
pub struct OctEncoded<T>(#[serde(deserialize_with = "deserialize")] pub T)
where
    T: ParseInt + fmt::Octal;

/// Wrapper type to force deserialization assuming decimal encoding.
#[derive(Clone, Deserialize, Debug, PartialEq)]
pub struct DecEncoded<T>(#[serde(deserialize_with = "deserialize")] pub T)
where
    T: ParseInt + fmt::Display;

/// Wrapper type to force deserialization assuming hexadecimal encoding.
#[derive(Clone, Deserialize, Debug, PartialEq)]
pub struct HexEncoded<T>(#[serde(deserialize_with = "deserialize")] pub T)
where
    T: ParseInt + fmt::LowerHex;

macro_rules! impl_parse_int_enc {
    ($ty:ident, $radix:expr, $fmt:path, $prefix:expr) => {
        impl<T: ParseInt + $fmt> std::ops::Deref for $ty<T> {
            type Target = T;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl<T: ParseInt + $fmt> ParseInt for $ty<T> {
            type FromStrRadixErr = T::FromStrRadixErr;

            fn from_str_radix(src: &str, radix: u32) -> Result<Self, T::FromStrRadixErr> {
                Ok(Self(T::from_str_radix(src, radix)?))
            }

            fn from_str(src: &str) -> Result<Self, ParseIntError> {
                Self::from_str_radix(src, $radix).map_err(|e| e.into())
            }
        }

        impl<T: ParseInt + $fmt> fmt::Display for $ty<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
                write!(f, "{}", $prefix)?;
                <_ as $fmt>::fmt(&self.0, f)
            }
        }

        impl<T: ParseInt + $fmt> Serialize for $ty<T> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                serializer.serialize_str(&self.to_string())
            }
        }
    };
}

impl_parse_int_enc!(OctEncoded, 8, fmt::Octal, "0o");
impl_parse_int_enc!(DecEncoded, 10, fmt::Display, "");
impl_parse_int_enc!(HexEncoded, 16, fmt::LowerHex, "0x");

impl ParseInt for Vec<u8> {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        let mut bytes = vec![];
        for digit_bytes in src.as_bytes().rchunks(2) {
            let digits = std::str::from_utf8(digit_bytes).unwrap();
            bytes.push(u8::from_str_radix(digits, radix)?);
        }
        Ok(bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use serde::Deserialize;

    #[test]
    fn de_u8() -> Result<()> {
        #[derive(Debug, Deserialize)]
        struct TestData {
            #[serde(deserialize_with = "deserialize")]
            oct: OctEncoded<u8>,
            #[serde(deserialize_with = "deserialize")]
            dec: DecEncoded<u8>,
            #[serde(deserialize_with = "deserialize")]
            hex: HexEncoded<u8>,
        }

        let data: TestData = deser_hjson::from_str(stringify!(
        {
            oct: "77",
            dec: "77",
            hex: "77"
        }))?;

        assert_eq!(*data.oct, 63);
        assert_eq!(*data.dec, 77);
        assert_eq!(*data.hex, 119);
        Ok(())
    }

    #[test]
    fn byte_field_test() {
        assert_eq!(Vec::from_str("0x1"), Ok(vec![0x1]));
        assert_eq!(
            Vec::from_str("0x0706050403020100"),
            Ok(vec![0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07])
        );
        assert_eq!(
            u64::from_ne_bytes(
                Vec::from_str("0x0706050403020100")
                    .unwrap()
                    .try_into()
                    .unwrap()
            ),
            u64::from_str("0x0706050403020100").unwrap()
        );
        assert!(Vec::from_str("-1").is_err());
    }
}
