// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use cryptoki::types::Ulong;
use once_cell::sync::OnceCell;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::convert::TryFrom;

use crate::util::attribute::{
    AttributeError, CertificateType, KeyType, MechanismType, ObjectClass,
};
use crate::util::escape::{as_hex, escape, unescape};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Redacted {
    RedactedByHsm,
    RedactedByTool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(untagged)]
pub enum AttrData {
    #[default]
    None,
    Bool(bool),
    Ulong(u64),
    CertificateType(CertificateType),
    KeyType(KeyType),
    MechanismType(MechanismType),
    ObjectClass(ObjectClass),
    Redacted(Redacted),
    Str(String),
    List(Vec<AttrData>),
}

impl From<bool> for AttrData {
    fn from(v: bool) -> Self {
        AttrData::Bool(v)
    }
}

impl TryFrom<&AttrData> for bool {
    type Error = AttributeError;
    fn try_from(a: &AttrData) -> Result<Self, Self::Error> {
        match a {
            AttrData::Bool(v) => Ok(*v),
            _ => Err(AttributeError::InvalidDataType),
        }
    }
}

impl From<u64> for AttrData {
    fn from(v: u64) -> Self {
        AttrData::Ulong(v)
    }
}

impl From<Ulong> for AttrData {
    fn from(v: Ulong) -> Self {
        AttrData::Ulong(*v)
    }
}

impl TryFrom<&AttrData> for u64 {
    type Error = AttributeError;
    fn try_from(a: &AttrData) -> Result<Self, Self::Error> {
        match a {
            AttrData::Ulong(v) => Ok(*v),
            _ => Err(AttributeError::InvalidDataType),
        }
    }
}

impl TryFrom<&AttrData> for Ulong {
    type Error = AttributeError;
    fn try_from(a: &AttrData) -> Result<Self, Self::Error> {
        match a {
            AttrData::Ulong(v) => Ok(Ulong::from(*v)),
            _ => Err(AttributeError::InvalidDataType),
        }
    }
}

impl From<&[u8]> for AttrData {
    fn from(v: &[u8]) -> Self {
        AttrData::Str(as_hex(v))
    }
}

pub fn unhex(ch: u8) -> u8 {
    match ch {
        b'0'..=b'9' => ch - b'0',
        b'A'..=b'F' => ch - b'A' + 10,
        b'a'..=b'f' => ch - b'a' + 10,
        _ => unreachable!(),
    }
}

impl TryFrom<&AttrData> for Vec<u8> {
    type Error = AttributeError;
    fn try_from(a: &AttrData) -> Result<Self, Self::Error> {
        static HEX: OnceCell<Regex> = OnceCell::new();
        match a {
            AttrData::Str(v) => {
                let hex =
                    HEX.get_or_init(|| Regex::new("^[0-9A-Fa-f]{2}(:[0-9A-Fa-f]{2})*$").unwrap());
                if hex.is_match(v) {
                    // The format of a hex string is "01:23:45:67[:...]".
                    // Take chunks of 3.  The regex guarantees that the
                    // hex string is composed only of ASCII characters and we
                    // can therefore view the str as bytes.
                    Ok(v.as_bytes()
                        .chunks(3)
                        .map(|ch| (unhex(ch[0]) << 4) | unhex(ch[1]))
                        .collect())
                } else {
                    Ok(unescape(v).map_err(|_| AttributeError::EncodingError)?)
                }
            }
            _ => Err(AttributeError::InvalidDataType),
        }
    }
}

impl AttrData {
    pub fn is_none(&self) -> bool {
        self == &AttrData::None
    }
    pub fn from_ascii_bytes(v: &[u8]) -> Self {
        AttrData::Str(escape(v))
    }

    pub fn try_str(&self) -> Result<&str, AttributeError> {
        match self {
            AttrData::Str(v) => Ok(v.as_str()),
            _ => Err(AttributeError::InvalidDataType),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn test_bool() -> Result<()> {
        let b = AttrData::from(true);
        assert!(bool::try_from(&b)?);
        assert!(u64::try_from(&b).is_err());
        assert!(Ulong::try_from(&b).is_err());
        assert!(Vec::<u8>::try_from(&b).is_err());
        assert!(b.try_str().is_err());
        Ok(())
    }

    #[test]
    fn test_ulong() -> Result<()> {
        let b = AttrData::from(12345u64);
        assert!(bool::try_from(&b).is_err());
        assert_eq!(u64::try_from(&b)?, 12345);
        assert_eq!(Ulong::try_from(&b)?, Ulong::from(12345));
        assert!(Vec::<u8>::try_from(&b).is_err());
        assert!(b.try_str().is_err());
        Ok(())
    }

    #[test]
    fn test_str() -> Result<()> {
        let data = vec![0x12u8, 0x34u8, 0x56u8, 0x78u8];
        let b = AttrData::from(data.as_slice());
        assert!(bool::try_from(&b).is_err());
        assert!(u64::try_from(&b).is_err());
        assert!(Ulong::try_from(&b).is_err());
        assert_eq!(Vec::<u8>::try_from(&b)?, &[0x12, 0x34, 0x56, 0x78]);
        assert_eq!(b.try_str()?, "12:34:56:78");
        Ok(())
    }
}
