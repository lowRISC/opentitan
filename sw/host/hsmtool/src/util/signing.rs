// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::mechanism::Mechanism;
use rsa::pkcs1v15::Pkcs1v15Sign;
use serde::{Deserialize, Serialize};
use sha2::digest::const_oid::AssociatedOid;
use sha2::digest::Digest;
use sha2::Sha256;
use std::str::FromStr;

use crate::error::HsmError;
use crate::util::attribute::KeyType;
use crate::util::helper::parse_range;

/// Specify the type of data being signed or verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SignData {
    /// The data to be signed is plain text.
    /// The data will be hashed and padded as specified by the signing algorithm.
    #[serde(alias = "plain-text")]
    PlainText,
    /// The data to be signed is a SHA-256 hash.
    /// The data will be padded as specified by the signing algorithm.
    #[serde(alias = "sha256-hash")]
    Sha256Hash,
    /// The data is raw and will be passed directly to the signing functions.
    #[serde(alias = "raw")]
    Raw,
    /// The data to be signed is plain text.
    /// A slice of the data will be hashed and padded as specified by the signing algorithm.
    #[serde(alias = "slice")]
    Slice(usize, usize),
}

impl FromStr for SignData {
    type Err = anyhow::Error;
    fn from_str(input: &str) -> Result<Self> {
        if input.eq_ignore_ascii_case("plain-text") {
            Ok(SignData::PlainText)
        } else if input.eq_ignore_ascii_case("sha256-hash") {
            Ok(SignData::Sha256Hash)
        } else if input.eq_ignore_ascii_case("raw") {
            Ok(SignData::Raw)
        } else if input[..6].eq_ignore_ascii_case("slice:") {
            let r = parse_range(&input[6..])?;
            Ok(SignData::Slice(r.start, r.end))
        } else {
            Err(HsmError::Unsupported(format!("invalid variant: {input}")).into())
        }
    }
}

impl SignData {
    pub const HELP: &'static str = "[allowed values: plain-text, sha256-hash, raw, slice:m..n]";
    /// Prepare `input` data for signing or verification.
    pub fn prepare(&self, keytype: KeyType, input: &[u8], little_endian: bool) -> Result<Vec<u8>> {
        match keytype {
            KeyType::Rsa => match self {
                // Data is plaintext: hash, then add PKCSv1.5 padding.
                SignData::PlainText => {
                    Self::pkcs15sign::<Sha256>(&Self::data_plain_text(input, false)?)
                }
                // Data is already hashed: add PKCSv1.5 padding.
                // If the `little_endian` flag is true, we assume the pre-hashed input came
                // from opentitantool, which writes out the hash in little endian order,
                // and therefore, needs to be reversed before the signing operation.
                SignData::Sha256Hash => {
                    Self::pkcs15sign::<Sha256>(&Self::data_raw(input, little_endian)?)
                }
                // Raw data requires no transformation.
                SignData::Raw => Self::data_raw(input, false),
                // Data is a slice of plaintext: hash, then add PKCSv1.5 padding.
                SignData::Slice(a, b) => {
                    Self::pkcs15sign::<Sha256>(&Self::data_plain_text(&input[*a..*b], false)?)
                }
            },
            KeyType::Ec => match self {
                // Data is plaintext: hash.
                SignData::PlainText => Self::data_plain_text(input, false),
                // Data is already hashed: no transformation needed.
                // If the `little_endian` flag is true, we assume the pre-hashed input came
                // from opentitantool, which writes out the hash in little endian order,
                // and therefore, needs to be reversed before the signing operation.
                SignData::Sha256Hash => Self::data_raw(input, little_endian),
                // Raw data requires no transformation.
                SignData::Raw => Self::data_raw(input, false),
                // Data is a slice of plaintext: hash.
                SignData::Slice(a, b) => Self::data_plain_text(&input[*a..*b], false),
            },
            _ => Err(HsmError::Unsupported("SignData prepare for {keytype:?}".into()).into()),
        }
    }

    /// Return the `Mechanism` needed during signing or verification.
    pub fn mechanism(&self, keytype: KeyType) -> Result<Mechanism> {
        match keytype {
            KeyType::Rsa => match self {
                SignData::PlainText => Ok(Mechanism::RsaPkcs),
                SignData::Sha256Hash => Ok(Mechanism::RsaPkcs),
                SignData::Raw => Err(HsmError::Unsupported(
                    "rust-cryptoki Mechanism doesn't include RSA_X_509".into(),
                )
                .into()),
                SignData::Slice(_, _) => Ok(Mechanism::RsaPkcs),
            },
            KeyType::Ec => match self {
                SignData::PlainText => Ok(Mechanism::Ecdsa),
                SignData::Sha256Hash => Ok(Mechanism::Ecdsa),
                SignData::Raw => Ok(Mechanism::Ecdsa),
                SignData::Slice(_, _) => Ok(Mechanism::Ecdsa),
            },
            _ => Err(HsmError::Unsupported("No mechanism for {keytype:?}".into()).into()),
        }
    }

    fn data_raw(input: &[u8], little_endian: bool) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        result.extend_from_slice(input);
        if little_endian {
            result.reverse();
        }
        Ok(result)
    }

    fn pkcs15sign<D>(input: &[u8]) -> Result<Vec<u8>>
    where
        D: Digest + AssociatedOid,
    {
        let s = Pkcs1v15Sign::new::<D>();
        let hash_len = s.hash_len.unwrap();
        if hash_len != input.len() {
            return Err(HsmError::HashSizeError(hash_len, input.len()).into());
        }
        let mut result = Vec::new();
        result.extend_from_slice(&s.prefix);
        result.extend_from_slice(input);
        Ok(result)
    }

    fn data_plain_text(input: &[u8], little_endian: bool) -> Result<Vec<u8>> {
        let mut result = Sha256::digest(input).as_slice().to_vec();
        if little_endian {
            result.reverse();
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw() -> Result<()> {
        let result = SignData::Raw.prepare(KeyType::Rsa, b"abc123", false)?;
        assert_eq!(result, b"abc123");
        Ok(())
    }

    #[test]
    fn test_plain_text() -> Result<()> {
        let result = SignData::PlainText.prepare(
            KeyType::Rsa,
            b"The quick brown fox jumped over the lazy dog",
            false,
        )?;
        assert_eq!(hex::encode(result),
            "3031300d0609608648016503040201050004207d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69"
        );

        let result = SignData::PlainText.prepare(
            KeyType::Ec,
            b"The quick brown fox jumped over the lazy dog",
            false,
        )?;
        assert_eq!(
            hex::encode(result),
            "7d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69",
        );
        Ok(())
    }

    #[test]
    fn test_hashed() -> Result<()> {
        let input =
            hex::decode("7d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69")?;
        let result = SignData::Sha256Hash.prepare(KeyType::Rsa, &input, false)?;
        assert_eq!(hex::encode(result),
            "3031300d0609608648016503040201050004207d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69"
        );

        assert!(SignData::Sha256Hash
            .prepare(KeyType::Rsa, b"", false)
            .is_err());
        Ok(())
    }

    #[test]
    fn test_slice() -> Result<()> {
        let result = SignData::Slice(0, 3).prepare(
            KeyType::Ec,
            b"The quick brown fox jumped over the lazy dog",
            false,
        )?;
        assert_eq!(
            hex::encode(result),
            // Hash of "The".
            "b344d80e24a3679999fa964450b34bc24d1578a35509f934c1418b0a20d21a67",
        );
        Ok(())
    }
}
