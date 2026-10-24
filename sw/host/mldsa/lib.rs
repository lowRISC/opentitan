// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod error;
mod key;
mod variants;

pub use error::MldsaError;
pub use key::{MldsaPublicKey, MldsaSecretKey};
pub use variants::MldsaParameterSet;

use std::path::Path;
use strum::{Display, EnumString};

/// Encoding of an ML-DSA key file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum KeyFormat {
    /// PEM encoded PKCS#8 / SubjectPublicKeyInfo.
    #[default]
    #[strum(serialize = "pem")]
    Pem,
    /// DER encoded PKCS#8 / SubjectPublicKeyInfo.
    #[strum(serialize = "der")]
    Der,
}

impl KeyFormat {
    /// File extension of a private key in this format.
    pub fn ext(&self) -> &'static str {
        match self {
            Self::Pem => "pem",
            Self::Der => "der",
        }
    }

    /// File extension of a public key in this format.
    pub fn pub_ext(&self) -> &'static str {
        match self {
            Self::Pem => "pub.pem",
            Self::Der => "pub.der",
        }
    }
}

/// Decode an ML-DSA key from its DER or PEM encoding.
pub trait DecodeKey: Sized {
    /// Deserialize the key from its DER encoding.
    fn from_der(der: &[u8]) -> Result<Self, MldsaError>;

    /// Deserialize the key from raw bytes representing the PEM file.
    fn from_pem_bytes(pem: &[u8]) -> Result<Self, MldsaError>;

    /// Deserialize the key from the string contents of the PEM file.
    fn from_pem(pem: &str) -> Result<Self, MldsaError> {
        Self::from_pem_bytes(pem.as_bytes())
    }

    /// Read a PEM or DER file and deserialize it into an ML-DSA key.
    fn from_file<P: AsRef<Path>>(filename: P) -> Result<Self, MldsaError> {
        let bytes = std::fs::read(filename)?;
        if bytes.trim_ascii_start().starts_with(b"-----BEGIN") {
            Self::from_pem_bytes(&bytes)
        } else {
            Self::from_der(&bytes)
        }
    }
}

/// Encode an ML-DSA key into its DER or PEM encoding.
pub trait EncodeKey {
    /// Serialize the key into its DER encoding.
    fn to_der(&self) -> Result<Vec<u8>, MldsaError>;

    /// Serialize the key into a PEM encoded string.
    fn to_pem(&self) -> Result<String, MldsaError>;

    /// Serialize the key in the given format and write it at the given path.
    fn write_file<P: AsRef<Path>>(&self, filename: P, format: KeyFormat) -> Result<(), MldsaError> {
        match format {
            KeyFormat::Pem => std::fs::write(filename, self.to_pem()?)?,
            KeyFormat::Der => std::fs::write(filename, self.to_der()?)?,
        }
        Ok(())
    }
}
