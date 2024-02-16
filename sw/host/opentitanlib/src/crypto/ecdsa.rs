// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use ecdsa::elliptic_curve::pkcs8::{DecodePrivateKey, EncodePrivateKey};
use ecdsa::elliptic_curve::pkcs8::{DecodePublicKey, EncodePublicKey};
use ecdsa::signature::hazmat::PrehashVerifier;
use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
use rand::rngs::OsRng;
use serde::Serialize;
use serde_annotate::Annotate;
use std::path::Path;

use crate::crypto::sha256::Sha256Digest;

pub struct EcdsaPrivateKey {
    pub key: SigningKey,
}

pub struct EcdsaPublicKey {
    pub key: VerifyingKey,
}

#[derive(Debug, Serialize, Annotate)]
pub struct EcdsaRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub x: Vec<u8>,
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub y: Vec<u8>,
}

impl Default for EcdsaPrivateKey {
    fn default() -> Self {
        Self::new()
    }
}

impl EcdsaPrivateKey {
    pub fn new() -> Self {
        Self {
            key: SigningKey::random(&mut OsRng),
        }
    }

    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        self.key.write_pkcs8_der_file(path)?;
        Ok(())
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let key = SigningKey::read_pkcs8_der_file(path)?;
        Ok(Self { key })
    }

    pub fn public_key(&self) -> EcdsaPublicKey {
        EcdsaPublicKey {
            key: *self.key.verifying_key(),
        }
    }

    pub fn sign(&self, digest: &Sha256Digest) -> Result<Vec<u8>> {
        let (sig, _) = self.key.sign_prehash_recoverable(&digest.to_be_bytes())?;
        let bytes = sig.to_bytes().as_slice().to_vec();
        Ok(bytes)
    }
}

impl EcdsaPublicKey {
    pub fn save(&self, path: impl AsRef<Path>) -> Result<()> {
        self.key.write_public_key_der_file(path)?;
        Ok(())
    }

    pub fn load(path: impl AsRef<Path>) -> Result<Self> {
        let key = VerifyingKey::read_public_key_der_file(path)?;
        Ok(Self { key })
    }

    pub fn to_raw(&self) -> EcdsaRawPublicKey {
        let point = self.key.to_encoded_point(false);
        EcdsaRawPublicKey {
            x: point.x().unwrap().as_slice().to_vec(),
            y: point.y().unwrap().as_slice().to_vec(),
        }
    }

    pub fn verify(&self, digest: &Sha256Digest, signature: &[u8]) -> Result<()> {
        let signature = Signature::from_slice(signature)?;
        self.key.verify_prehash(&digest.to_be_bytes(), &signature)?;
        Ok(())
    }
}
