// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
use std::io::{Read, Write};
use std::path::Path;

use anyhow::Result;

use signature::{Keypair, Signer, Verifier};

use pqcrypto_sphincsplus::sphincsshake256128ssimple as spx;
use pqcrypto_traits::sign::DetachedSignature;
use pqcrypto_traits::sign::PublicKey;
use pqcrypto_traits::sign::SecretKey;

use crate::util::bigint::fixed_size_bigint;
use crate::util::file::{FromReader, PemSerilizable, ToWriter};

// Signature and key sizes taken from Table 8 on page 57 of the SPHINCS+ Round 3 Specification:
// https://sphincs.org/data/sphincs+-round3-specification.pdf
const PUBLIC_KEY_BYTE_LEN: usize = 32;
const SECRET_KEY_BYTE_LEN: usize = 64;
const SIGNATURE_BIT_LEN: usize = 7856 * 8;
fixed_size_bigint!(Signature, at_most SIGNATURE_BIT_LEN);

#[derive(Clone)]
pub enum SpxKey {
    Public(SpxPublicKey),
    Private(SpxKeypair),
}

impl Keypair for SpxKey {
    type VerifyingKey = SpxPublicKey;

    fn verifying_key(&self) -> Self::VerifyingKey {
        match self {
            SpxKey::Public(pk) => pk.clone(),
            SpxKey::Private(sk) => sk.verifying_key(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SpxError {
    #[error("SPHINCS+ key load error\nPublic key: {0}\nKey pair: {1}")]
    LoadError(anyhow::Error, anyhow::Error),
}

/// Given the path to either a SPHINCS+ public key or full keypair returns the appropriate `SpxKey`.
pub fn load_spx_key(key_file: &Path) -> Result<SpxKey> {
    Ok(match SpxKeypair::read_pem_file(key_file) {
        Ok(sk) => SpxKey::Private(sk),
        Err(e1) => match SpxPublicKey::read_pem_file(key_file) {
            Ok(pk) => SpxKey::Public(pk),
            Err(e2) => Err(SpxError::LoadError(e1, e2))?,
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
}

impl Keypair for SpxKeypair {
    type VerifyingKey = SpxPublicKey;

    fn verifying_key(&self) -> Self::VerifyingKey {
        SpxPublicKey(self.pk)
    }
}

impl Signer<Signature> for SpxKeypair {
    fn try_sign(&self, msg: &[u8]) -> std::result::Result<Signature, signature::Error> {
        let sm = spx::detached_sign(msg, &self.sk);
        Ok(Signature::from_le_bytes(sm.as_bytes()).unwrap())
    }
}

impl ToWriter for SpxKeypair {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        // Write out the keypair as a fixed length byte-string consisting of the public key
        // concatenated with the secret key.
        //
        // Note: The SPHINCS+ secret key contains the public key, but since pqcrypto doesn't expose
        // any way to transmute between key types we duplicate the public portion rather than
        // splicing the raw bytes.
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

    pub fn as_bytes(&self) -> Vec<u8> {
        self.0.as_bytes().to_owned()
    }
}

impl Verifier<Signature> for SpxPublicKey {
    fn verify(
        &self,
        msg: &[u8],
        signature: &Signature,
    ) -> std::result::Result<(), signature::Error> {
        spx::verify_detached_signature(
            &spx::DetachedSignature::from_bytes(&signature.0.to_le_bytes()).unwrap(),
            msg,
            &self.0,
        )
        .map_err(signature::Error::from_source)
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

impl ToWriter for Signature {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(&self.to_le_bytes())?;
        Ok(())
    }
}

impl FromReader for Signature {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut buf = [0u8; SIGNATURE_BIT_LEN / 8];
        let len = r.read(&mut buf)?;
        Ok(Signature::from_le_bytes(&buf[..len])?)
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
        assert!(keypair.verifying_key().verify(msg, &sig).is_ok());
    }
}
