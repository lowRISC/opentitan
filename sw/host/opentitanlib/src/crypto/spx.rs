// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use pqcrypto_sphincsplus::sphincsshake256128ssimple as spx;
use pqcrypto_traits::sign::DetachedSignature;
use pqcrypto_traits::sign::PublicKey;
use pqcrypto_traits::sign::SecretKey;

use super::Error;
use crate::util::bigint::fixed_size_bigint;
use crate::util::file::{FromReader, PemSerilizable, ToWriter};

// Signature and key sizes taken from Table 8 on page 57 of the SPHINCS+ Round 3 Specification:
// https://sphincs.org/data/sphincs+-round3-specification.pdf
const PUBLIC_KEY_BYTE_LEN: usize = 32;
const SECRET_KEY_BYTE_LEN: usize = 64;
const SIGNATURE_BIT_LEN: usize = 7856 * 8;
fixed_size_bigint!(Signature, at_most SIGNATURE_BIT_LEN);

/// Trait for implementing public key operations.
pub trait SpxPublicKeyPart {
    /// Returns the public key component.
    fn pk(&self) -> &spx::PublicKey;

    fn pk_as_bytes(&self) -> &[u8] {
        self.pk().as_bytes()
    }

    fn pk_len(&self) -> usize {
        self.pk_as_bytes().len()
    }

    /// Verify a message signature, returning Ok(()) if the signature matches.
    fn verify(&self, message: &[u8], sig: &SpxSignature) -> Result<()> {
        spx::verify_detached_signature(
            &spx::DetachedSignature::from_bytes(&sig.0.to_le_bytes())?,
            message,
            self.pk(),
        )?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum SpxKey {
    Public(SpxPublicKey),
    Private(SpxKeypair),
}

impl SpxPublicKeyPart for SpxKey {
    fn pk(&self) -> &spx::PublicKey {
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
    pk: spx::PublicKey,
    sk: spx::SecretKey,
}

impl SpxKeypair {
    /// Generates a new SPHINCS+ keypair.
    pub fn generate() -> Self {
        let (pk, sk) = spx::keypair();
        SpxKeypair { pk, sk }
    }

    /// Sign `message` using the secret key.
    pub fn sign(&self, message: &[u8]) -> SpxSignature {
        let sm = spx::detached_sign(message, &self.sk);
        SpxSignature(Signature::from_le_bytes(sm.as_bytes()).unwrap())
    }

    /// Consumes this keypair and returns the corrisponding public key.
    pub fn into_public_key(self) -> SpxPublicKey {
        SpxPublicKey(self.pk)
    }
}

impl SpxPublicKeyPart for SpxKeypair {
    fn pk(&self) -> &spx::PublicKey {
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
        let mut buf = [0u8; PUBLIC_KEY_BYTE_LEN + SECRET_KEY_BYTE_LEN];
        r.read_exact(&mut buf)?;
        Ok(SpxKeypair {
            pk: spx::PublicKey::from_bytes(&buf[..PUBLIC_KEY_BYTE_LEN])?,
            sk: spx::SecretKey::from_bytes(&buf[PUBLIC_KEY_BYTE_LEN..])?,
        })
    }
}

impl PemSerilizable for SpxKeypair {
    fn label() -> &'static str {
        "RAW SPHINCS+ PRIVATE KEY"
    }
}

/// Wrapper for a SPHINCS+ public key.
#[derive(Clone)]
pub struct SpxPublicKey(spx::PublicKey);

impl SpxPublicKey {
    pub fn from_bytes(b: &[u8]) -> Result<Self> {
        Ok(SpxPublicKey(spx::PublicKey::from_bytes(b)?))
    }
}

impl SpxPublicKeyPart for SpxPublicKey {
    fn pk(&self) -> &spx::PublicKey {
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
        let mut buf = [0u8; PUBLIC_KEY_BYTE_LEN];
        r.read_exact(&mut buf)?;
        Ok(SpxPublicKey(spx::PublicKey::from_bytes(&buf)?))
    }
}

impl PemSerilizable for SpxPublicKey {
    fn label() -> &'static str {
        "RAW SPHINCS+ PUBLIC KEY"
    }
}

/// Wrapper for a SPHINCS+ signature.
#[derive(Clone)]
pub struct SpxSignature(pub Signature);

impl ToWriter for SpxSignature {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(&self.0.to_le_bytes())?;
        Ok(())
    }
}

impl FromReader for SpxSignature {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut buf = [0u8; SIGNATURE_BIT_LEN / 8];
        let len = r.read(&mut buf)?;
        Ok(SpxSignature(Signature::from_le_bytes(&buf[..len])?))
    }
}

impl ToString for SpxSignature {
    fn to_string(&self) -> String {
        self.0.to_string()
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

impl TryFrom<&spx::PublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: &spx::PublicKey) -> Result<Self, Self::Error> {
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
