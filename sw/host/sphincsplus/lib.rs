// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod error;
mod key;
mod signature;
mod variants;

pub use error::SpxError;
pub use key::{SpxDomain, SpxPublicKey, SpxSecretKey, SpxSignatureMode};
pub use signature::SpxRawSignature;
pub use variants::SphincsPlus;

use std::path::Path;

/// Decode a SPHINCS+ key stored in OpenTitan's custom legacy RAW PEM format.
pub trait DecodeKey: Sized {
    /// Deserialize the key from raw bytes representing the PEM file.
    fn from_pem_bytes(pem: &[u8]) -> Result<Self, SpxError>;

    /// Deserialize the key from the string contents of the PEM file.
    fn from_pem(pem: &str) -> Result<Self, SpxError> {
        Self::from_pem_bytes(pem.as_bytes())
    }

    /// Read a PEM file and deserialize it into a SPHINCS+ key.
    fn from_pem_file<P: AsRef<Path>>(pem_file: P) -> Result<Self, SpxError> {
        let pem = std::fs::read(pem_file).map_err(SpxError::Io)?;
        Self::from_pem_bytes(&pem)
    }
}

/// Encode a SPHINCS+ key into OpenTitan's custom legacy RAW PEM format.
pub trait EncodeKey {
    /// Serialize the key into the a PEM encoded string.
    fn to_pem(&self) -> Result<String, SpxError>;

    // Serialize the key into a PEM file and write it at the given path.
    fn write_pem_file<P: AsRef<Path>>(&self, filename: P) -> Result<(), SpxError> {
        let pem = self.to_pem()?;
        std::fs::write(filename, pem).map_err(SpxError::Io)
    }
}
