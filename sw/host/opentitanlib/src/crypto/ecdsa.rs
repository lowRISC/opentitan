// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use ecdsa::elliptic_curve::pkcs8::{DecodePrivateKey, EncodePrivateKey};
use ecdsa::elliptic_curve::pkcs8::{DecodePublicKey, EncodePublicKey};
use ecdsa::signature::hazmat::PrehashVerifier;
use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use super::Error;
use crate::crypto::sha256::{sha256, Sha256Digest};

pub struct EcdsaPrivateKey {
    pub key: SigningKey,
}

pub struct EcdsaPublicKey {
    pub key: VerifyingKey,
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

    pub fn sign(&self, digest: &Sha256Digest) -> Result<EcdsaRawSignature> {
        let (sig, _) = self.key.sign_prehash_recoverable(&digest.to_be_bytes())?;
        let bytes = sig.to_bytes();
        let half = bytes.len() / 2;
        // The signature bytes are (R || S).  Since opentitan is a little-endian
        // machine, we want to reverse the byte order of each component of the
        // signature.
        let mut r = Vec::new();
        r.extend(bytes[..half].iter().rev());
        let mut s = Vec::new();
        s.extend(bytes[half..].iter().rev());
        Ok(EcdsaRawSignature { r, s })
    }

    pub fn digest_and_sign(&self, data: &[u8]) -> Result<EcdsaRawSignature> {
        let digest = sha256(data);
        self.sign(&digest)
    }
}

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct EcdsaRawSignature {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub r: Vec<u8>,
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub s: Vec<u8>,
}

impl Default for EcdsaRawSignature {
    fn default() -> Self {
        Self {
            r: vec![0u8; 32],
            s: vec![0u8; 32],
        }
    }
}

impl TryFrom<&[u8]> for EcdsaRawSignature {
    type Error = Error;
    fn try_from(value: &[u8]) -> std::result::Result<Self, Self::Error> {
        if value.len() != 64 {
            return Err(Error::InvalidSignature(anyhow!(
                "bad length: {}",
                value.len()
            )));
        }
        let mut value = std::io::Cursor::new(value);
        EcdsaRawSignature::read(&mut value).map_err(Error::InvalidSignature)
    }
}

impl EcdsaRawSignature {
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut sig = Self::default();
        src.read_exact(&mut sig.r)?;
        src.read_exact(&mut sig.s)?;
        Ok(sig)
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.r.len() == 32,
            Error::InvalidSignature(anyhow!("bad r length: {}", self.r.len()))
        );
        ensure!(
            self.s.len() == 32,
            Error::InvalidSignature(anyhow!("bad s length: {}", self.s.len()))
        );
        dest.write_all(&self.r)?;
        dest.write_all(&self.s)?;
        Ok(())
    }

    pub fn to_vec(&self) -> Result<Vec<u8>> {
        let mut sig = Vec::new();
        self.write(&mut sig)?;
        Ok(sig)
    }

    pub fn is_empty(&self) -> bool {
        self.r.iter().all(|&v| v == 0) && self.s.iter().all(|&v| v == 0)
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

    pub fn verify(&self, digest: &Sha256Digest, signature: &EcdsaRawSignature) -> Result<()> {
        let mut bytes = signature.to_vec()?;
        let half = bytes.len() / 2;
        // The signature bytes are (R || S).  Since opentitan is a little-endian
        // machine, we expect the input signature to have R and S in
        // little-endian order.  Reverse the bytes back to big-endian ordering.
        bytes[..half].reverse();
        bytes[half..].reverse();
        let signature = Signature::from_slice(&bytes)?;
        self.key.verify_prehash(&digest.to_be_bytes(), &signature)?;
        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct EcdsaRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub x: Vec<u8>,
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub y: Vec<u8>,
}

impl Default for EcdsaRawPublicKey {
    fn default() -> Self {
        Self {
            x: vec![0u8; 32],
            y: vec![0u8; 32],
        }
    }
}

impl TryFrom<&EcdsaPublicKey> for EcdsaRawPublicKey {
    type Error = Error;
    fn try_from(v: &EcdsaPublicKey) -> Result<Self, Self::Error> {
        let point = v.key.to_encoded_point(false);
        // Since opentitan is a little-endian machine, we reverse the byte
        // order of the X and Y values.
        let mut x = point.x().unwrap().as_slice().to_vec();
        let mut y = point.y().unwrap().as_slice().to_vec();
        x.reverse();
        y.reverse();
        Ok(EcdsaRawPublicKey { x, y })
    }
}

impl FromStr for EcdsaRawPublicKey {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let key = EcdsaPublicKey::load(s)
            .with_context(|| format!("Failed to load {s}"))
            .map_err(Error::Other)?;
        EcdsaRawPublicKey::try_from(&key)
    }
}

impl EcdsaRawPublicKey {
    pub const SIZE: usize = 32 + 32;
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut key = Self::default();
        src.read_exact(&mut key.x)?;
        src.read_exact(&mut key.y)?;
        Ok(key)
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.x.len() == 32,
            Error::InvalidPublicKey(anyhow!("bad x length: {}", self.x.len()))
        );
        ensure!(
            self.y.len() == 32,
            Error::InvalidPublicKey(anyhow!("bad y length: {}", self.y.len()))
        );
        dest.write_all(&self.x)?;
        dest.write_all(&self.y)?;
        Ok(())
    }
}
