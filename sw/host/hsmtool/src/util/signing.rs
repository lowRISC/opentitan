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

use crate::error::HsmError;

/// Specify the type of data being signed or verified.
#[derive(clap::ValueEnum, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SignData {
    /// The data to be signed is plain text.
    /// The data will be hashed and padded according to PKCS#1 v1.5.
    #[serde(alias = "plain-text")]
    PlainText,
    /// The data to be signed is a SHA-256 hash.
    /// The data will have the PKCS#1 v1.5 prefix and padding added.
    #[serde(alias = "sha256-hash")]
    Sha256Hash,
    /// The data is raw and will be passed directly to the signing functions.
    #[serde(alias = "raw")]
    Raw,
}

impl SignData {
    /// Prepare `input` data for signing or verification.
    pub fn prepare(&self, input: &[u8]) -> Result<Vec<u8>> {
        match self {
            SignData::PlainText => Self::data_plain_text(input),
            SignData::Sha256Hash => Self::data_hashed::<Sha256>(input),
            SignData::Raw => Self::data_raw(input),
        }
    }

    /// Return the `Mechanism` needed during signing or verification.
    pub fn mechanism(&self) -> Result<Mechanism> {
        match self {
            SignData::PlainText => Ok(Mechanism::RsaPkcs),
            SignData::Sha256Hash => Ok(Mechanism::RsaPkcs),
            SignData::Raw => Err(HsmError::Unsupported(
                "rust-cryptoki Mechanism doesn't include RSA_X_509".into(),
            )
            .into()),
        }
    }

    fn data_raw(input: &[u8]) -> Result<Vec<u8>> {
        let mut result = Vec::new();
        result.extend_from_slice(input);
        Ok(result)
    }

    fn data_hashed<D>(input: &[u8]) -> Result<Vec<u8>>
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

    fn data_plain_text(input: &[u8]) -> Result<Vec<u8>> {
        let hash = Sha256::digest(input);
        Self::data_hashed::<Sha256>(&hash)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw() -> Result<()> {
        let result = SignData::Raw.prepare(b"abc123")?;
        assert_eq!(result, b"abc123");
        Ok(())
    }

    #[test]
    fn test_plain_text() -> Result<()> {
        let result =
            SignData::PlainText.prepare(b"The quick brown fox jumped over the lazy dog")?;
        assert_eq!(hex::encode(result),
            "3031300d0609608648016503040201050004207d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69"
        );
        Ok(())
    }

    #[test]
    fn test_hashed() -> Result<()> {
        let input =
            hex::decode("7d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69")?;
        let result = SignData::Sha256Hash.prepare(&input)?;
        assert_eq!(hex::encode(result),
            "3031300d0609608648016503040201050004207d38b5cd25a2baf85ad3bb5b9311383e671a8a142eb302b324d4a5fba8748c69"
        );

        assert!(SignData::Sha256Hash.prepare(b"").is_err());
        Ok(())
    }
}
