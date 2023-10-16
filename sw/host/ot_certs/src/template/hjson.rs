// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module contains Hjson-specific encodings of certificate template
//! components.
//!
//! They are kept separated here so that details of the representation of
//! templates on-disk (in Hjson) can change without the API of the template
//! structs changing.

use hex::FromHex;
use num_bigint_dig::BigUint as InnerBigUint;
use num_traits::{Num, ToPrimitive};
use serde::de;
use serde::{Deserialize, Deserializer};
use serde_with::DeserializeAs;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigUint {
    biguint: InnerBigUint,
}

impl From<BigUint> for InnerBigUint {
    fn from(value: BigUint) -> InnerBigUint {
        value.biguint
    }
}

// Helper trait to improve error messages for Value<T>.
pub trait DeserializeAsHelpMsg<T> {
    fn help_msg() -> &'static str;
    fn example() -> &'static str;
}

impl DeserializeAsHelpMsg<String> for String {
    fn help_msg() -> &'static str {
        "a string"
    }

    fn example() -> &'static str {
        "\"hello world\""
    }
}

// Deserialize BigUint as InnerBigUint. This is necessary because the default hjson
// parser really wants to parse numbers by itself and it won't handle big integers
// or any customization.
impl<'de> DeserializeAs<'de, InnerBigUint> for BigUint {
    fn deserialize_as<D>(deserializer: D) -> Result<InnerBigUint, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer
            .deserialize_str(BigUintVisitor)
            .map(InnerBigUint::from)
    }
}

impl DeserializeAsHelpMsg<InnerBigUint> for BigUint {
    fn help_msg() -> &'static str {
        "a string representing a non-negative integer (you can use the prefix '0x' for hexadecimal)"
    }

    fn example() -> &'static str {
        "410983 or 0x64567"
    }
}

// Same for u8, derserialize as BigUint and see if it fits.
impl<'de> DeserializeAs<'de, u8> for BigUint {
    fn deserialize_as<D>(deserializer: D) -> Result<u8, D::Error>
    where
        D: Deserializer<'de>,
    {
        let inner: InnerBigUint = BigUint::deserialize_as(deserializer)?;
        match inner.to_u8() {
            Some(x) => Ok(x),
            None => Err(de::Error::custom(format!(
                "expected 8-bit integer but {} is too large",
                inner
            ))),
        }
    }
}

impl DeserializeAsHelpMsg<u8> for BigUint {
    fn help_msg() -> &'static str {
        "a string representing a non-negative 8-bit integer (you can use the prefix '0x' for hexadecimal)"
    }

    fn example() -> &'static str {
        "123 or 0x7b"
    }
}

struct BigUintVisitor;

impl<'de> serde::de::Visitor<'de> for BigUintVisitor {
    type Value = BigUint;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a non-negative integer, you can use the prefix '0x' for hexadecimal")
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        // Unless the string starts with '0x', expect a decimal string.
        let (radix, s) = s.strip_prefix("0x").map_or_else(|| (10, s), |s| (16, s));
        InnerBigUint::from_str_radix(s, radix)
            .map_err(de::Error::custom)
            .map(|biguint| BigUint { biguint })
    }
}

pub struct HexString;

/// Deserialization of a `Value<Vec<u8>>` from a string of hex digits.
impl<'de> DeserializeAs<'de, Vec<u8>> for HexString {
    fn deserialize_as<D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Vec::<u8>::from_hex(s)
            .map_err(|err| de::Error::custom(format!("could not parse hexstring: {}", err)))
    }
}

impl DeserializeAsHelpMsg<Vec<u8>> for HexString {
    fn help_msg() -> &'static str {
        "a hexstring (a string of hexadecimal characters representing a byte array)"
    }

    fn example() -> &'static str {
        "ff8702"
    }
}

impl<T> DeserializeAsHelpMsg<T> for serde_with::Same
where
    T: DeserializeAsHelpMsg<T>,
{
    fn help_msg() -> &'static str {
        T::help_msg()
    }

    fn example() -> &'static str {
        T::example()
    }
}
