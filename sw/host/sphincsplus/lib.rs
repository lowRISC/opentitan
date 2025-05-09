// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

mod error;
mod key;
mod signature;
mod variants;

pub use error::SpxError;
pub use key::{SpxDomain, SpxPublicKey, SpxSecretKey};
pub use signature::SpxRawSignature;
pub use variants::SphincsPlus;

use std::path::Path;

pub trait DecodeKey: Sized {
    fn from_pem(s: &str) -> Result<Self, SpxError>;
    fn read_pem_file<P: AsRef<Path>>(filename: P) -> Result<Self, SpxError> {
        let s = std::fs::read_to_string(filename).map_err(SpxError::Io)?;
        Self::from_pem(&s)
    }
}

pub trait EncodeKey {
    fn to_pem(&self) -> Result<String, SpxError>;
    fn write_pem_file<P: AsRef<Path>>(&self, filename: P) -> Result<(), SpxError> {
        let s = self.to_pem()?;
        std::fs::write(filename, s).map_err(SpxError::Io)
    }
}
