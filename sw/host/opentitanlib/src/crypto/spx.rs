// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use sphincsplus::{SPX_PUBLIC_KEY_BYTES, SPX_SECRET_KEY_BYTES, SPX_SIGNATURE_BYTES};

use super::Error;
use crate::util::file::{FromReader, PemSerilizable, ToWriter};

/// Trait for implementing public key operations.
pub trait SpxPublicKeyPart {
    /// Returns the public key component.
    fn pk(&self) -> &sphincsplus::SpxPublicKey;

    fn pk_as_bytes(&self) -> &[u8] {
        self.pk().as_bytes()
    }

    fn pk_len(&self) -> usize {
        self.pk_as_bytes().len()
    }

    /// Verify a message signature, returning Ok(()) if the signature matches.
    fn verify(&self, message: &[u8], sig: &SpxSignature) -> Result<()> {
        Ok(sphincsplus::spx_verify(self.pk(), &sig.0, message)?)
    }
}

#[derive(Clone)]
pub enum SpxKey {
    Public(SpxPublicKey),
    Private(SpxKeypair),
}

impl SpxPublicKeyPart for SpxKey {
    fn pk(&self) -> &sphincsplus::SpxPublicKey {
        match self {
            SpxKey::Public(k) => k.pk(),
            SpxKey::Private(k) => k.pk(),
        }
    }
}

/// Given the path to either a SPHINCS+ public key or full keypair returns the appropriate `SpxKey`.
pub fn load_spx_key(key_file: &Path) -> Result<SpxKey> {
    Ok(match SpxKeypair::read_pem_file(key_file) {
        Ok(sk) => SpxKey::Private(sk),
        Err(_) => match SpxPublicKey::read_pem_file(key_file) {
            Ok(pk) => SpxKey::Public(pk),
            Err(e2) => Err(Error::ReadFailed {
                file: key_file.to_owned(),
                source: anyhow!(e2),
            })?,
        },
    })
}

/// A SPHINCS+ keypair consisting of the public and secret keys.
#[derive(Clone)]
pub struct SpxKeypair {
    pk: sphincsplus::SpxPublicKey,
    sk: sphincsplus::SpxSecretKey,
}

impl SpxKeypair {
    /// Generates a new SPHINCS+ keypair.
    pub fn generate() -> Self {
        let (pk, sk) = sphincsplus::spx_keypair_generate().unwrap();
        SpxKeypair { pk, sk }
    }

    /// Sign `message` using the secret key.
    pub fn sign(&self, message: &[u8]) -> SpxSignature {
        SpxSignature(sphincsplus::spx_sign(&self.sk, message).unwrap())
    }

    /// Consumes this keypair and returns the corrisponding public key.
    pub fn into_public_key(self) -> SpxPublicKey {
        SpxPublicKey(self.pk)
    }
}

impl SpxPublicKeyPart for SpxKeypair {
    fn pk(&self) -> &sphincsplus::SpxPublicKey {
        &self.pk
    }
}

impl ToWriter for SpxKeypair {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        // Write out the keypair as a fixed length byte-string consisting of the public key
        // concatenated with the secret key.
        w.write_all(self.pk.as_bytes())?;
        w.write_all(self.sk.as_bytes())?;
        Ok(())
    }
}

impl FromReader for SpxKeypair {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        // Read in the buffer as a fixed length byte-string consisting of the public key
        // concatenated with the secret key.
        let mut pk_buf = [0u8; SPX_PUBLIC_KEY_BYTES];
        r.read_exact(&mut pk_buf)?;
        let pk = sphincsplus::SpxPublicKey::try_from(pk_buf)?;
        let mut sk_buf = [0u8; SPX_SECRET_KEY_BYTES];
        r.read_exact(&mut sk_buf)?;
        let sk = sphincsplus::SpxSecretKey::try_from(sk_buf)?;
        Ok(SpxKeypair { pk, sk })
    }
}

impl PemSerilizable for SpxKeypair {
    fn label() -> &'static str {
        "RAW SPHINCS+ PRIVATE KEY"
    }
}

/// Wrapper for a SPHINCS+ public key.
#[derive(Clone)]
pub struct SpxPublicKey(sphincsplus::SpxPublicKey);

impl SpxPublicKeyPart for SpxPublicKey {
    fn pk(&self) -> &sphincsplus::SpxPublicKey {
        &self.0
    }
}

impl ToWriter for SpxPublicKey {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(self.0.as_bytes())?;
        Ok(())
    }
}

impl FromReader for SpxPublicKey {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut pk_buf = [0u8; SPX_PUBLIC_KEY_BYTES];
        r.read_exact(&mut pk_buf)?;
        let pk = sphincsplus::SpxPublicKey::try_from(pk_buf)?;
        Ok(SpxPublicKey(pk))
    }
}

impl PemSerilizable for SpxPublicKey {
    fn label() -> &'static str {
        "RAW SPHINCS+ PUBLIC KEY"
    }
}

/// Wrapper for a SPHINCS+ signature.
#[derive(Clone)]
pub struct SpxSignature(sphincsplus::SpxSignature);

impl ToWriter for SpxSignature {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(self.0.as_bytes())?;
        Ok(())
    }
}

impl FromReader for SpxSignature {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut sig_buf = [0u8; SPX_SIGNATURE_BYTES];
        r.read_exact(&mut sig_buf)?;
        let sig = sphincsplus::SpxSignature::try_from(sig_buf)?;
        Ok(SpxSignature(sig))
    }
}

impl SpxSignature {
    pub fn sig_as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct SpxRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub key: Vec<u8>,
}

impl Default for SpxRawPublicKey {
    fn default() -> Self {
        Self { key: vec![0; 32] }
    }
}

impl TryFrom<&sphincsplus::SpxPublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: &sphincsplus::SpxPublicKey) -> Result<Self, Self::Error> {
        Ok(Self {
            key: v.as_bytes().to_vec(),
        })
    }
}

impl FromStr for SpxRawPublicKey {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let key = load_spx_key(s.as_ref())
            .with_context(|| format!("Failed to load {s}"))
            .map_err(Error::Other)?;
        SpxRawPublicKey::try_from(key.pk())
    }
}

impl SpxRawPublicKey {
    pub const SIZE: usize = 32;
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut key = Self::default();
        key.key.resize(32, 0);
        src.read_exact(&mut key.key)?;
        Ok(key)
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.key.len() == Self::SIZE,
            Error::InvalidPublicKey(anyhow!("bad key length: {}", self.key.len()))
        );
        dest.write_all(&self.key)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_spx_sign() {
        let msg = b"Test message";

        let keypair = SpxKeypair::generate();
        let sig = keypair.sign(msg);
        assert!(keypair.verify(msg, &sig).is_ok());
    }
}
