// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use thiserror::Error;

pub mod ecdsa;
pub mod rsa;
pub mod sha256;
pub mod spx;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Invalid public key: {0:?}")]
    InvalidPublicKey(#[source] anyhow::Error),
    #[error("Invalid DER file: {der}")]
    InvalidDerFile {
        der: PathBuf,
        #[source]
        source: anyhow::Error,
    },
    #[error("Read failed: {file}")]
    ReadFailed {
        file: PathBuf,
        #[source]
        source: anyhow::Error,
    },
    #[error("Write failed: {file}")]
    WriteFailed {
        file: PathBuf,
        #[source]
        source: anyhow::Error,
    },
    #[error("Generate failed")]
    GenerateFailed(#[source] anyhow::Error),
    #[error("Invalid signature")]
    InvalidSignature(#[source] anyhow::Error),
    #[error("Sign failed")]
    SignFailed(#[source] anyhow::Error),
    #[error("Verification failed")]
    VerifyFailed(#[source] anyhow::Error),
    #[error("Failed to compute key component")]
    KeyComponentComputeFailed,
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}
