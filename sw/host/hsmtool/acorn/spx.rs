// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use bitflags::bitflags;
use sphincsplus::SpxDomain;

#[derive(Debug, Default)]
pub struct KeyEntry {
    /// Alias of the key.
    pub alias: String,
    /// Unique identifier for the key.
    pub hash: Option<String>,
    /// Algorithm to be used with the key.
    pub algorithm: String,
    /// Domain to be used with the key (only when keys are restricted to a specific domain).
    pub domain: Option<SpxDomain>,
    /// Opaque representation of the private key material.
    pub private_blob: Vec<u8>,
    /// Exported private key material (only when GenerateFlags::EXPORT_PRIVATE is set).
    pub private_key: Vec<u8>,
}

#[derive(Debug, Default)]
pub struct KeyInfo {
    /// Unique identifier for the key.
    pub hash: String,
    /// Algorithm to be used with the key.
    pub algorithm: String,
    /// Domain to be used with the key (only when keys are restricted to a specific domain).
    pub domain: Option<SpxDomain>,
    /// Public key material.
    pub public_key: Vec<u8>,
    /// Opaque representation of the private key material.
    pub private_blob: Vec<u8>,
}

bitflags! {
    #[derive(Debug)]
    pub struct GenerateFlags: u32 {
        const NONE = 0;
        const OVERWRITE = 1 << acorn_bindgen::acorn_enum_generateFlags_acorn_enum_generateFlags_overwrite;
        const EXPORT_PRIVATE = 1 << acorn_bindgen::acorn_enum_generateFlags_acorn_enum_generateFlags_exportPrivate;
    }
}

pub trait SpxInterface {
    /// Get the version of the backend.
    fn get_version(&self) -> Result<String>;

    /// Get the version of the backend.
    fn list_keys(&self) -> Result<Vec<KeyEntry>>;

    /// Get the public key info.
    fn get_key_info(&self, alias: &str) -> Result<KeyInfo>;

    /// Generate a key pair.
    fn generate_key(
        &self,
        alias: &str,
        algorithm: &str,
        domain: SpxDomain,
        token: &str,
        flags: GenerateFlags,
    ) -> Result<KeyEntry>;

    /// Import a key pair.
    #[allow(clippy::too_many_arguments)]
    fn import_keypair(
        &self,
        alias: &str,
        algorithm: &str,
        domain: SpxDomain,
        token: &str,
        overwrite: bool,
        public_key: &[u8],
        private_key: &[u8],
    ) -> Result<KeyEntry>;

    /// Sign a message.
    fn sign(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
    ) -> Result<Vec<u8>>;

    /// Verify a message.
    fn verify(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool>;
}
