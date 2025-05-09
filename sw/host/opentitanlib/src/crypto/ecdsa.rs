// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use ecdsa::elliptic_curve::pkcs8::{DecodePrivateKey, EncodePrivateKey};
use ecdsa::elliptic_curve::pkcs8::{DecodePublicKey, EncodePublicKey};
use ecdsa::signature::hazmat::PrehashVerifier;
use ecdsa::Signature;
use p256::ecdsa::{SigningKey, VerifyingKey};
use p256::NistP256;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use sha2::digest::generic_array::GenericArray;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use super::Error;
use crate::crypto::sha256::Sha256Digest;

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
        let (sig, _) = self.key.sign_prehash_recoverable(digest.as_ref())?;
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
        self.sign(&Sha256Digest::hash(data))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Annotate)]
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
        if value.len() != Self::SIZE {
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
    const SIZE: usize = 64;

    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut sig = Self::default();
        src.read_exact(&mut sig.r)?;
        src.read_exact(&mut sig.s)?;
        Ok(sig)
    }

    pub fn read_from_file(path: &Path) -> Result<EcdsaRawSignature> {
        let mut file =
            File::open(path).with_context(|| format!("Failed to read file: {path:?}"))?;
        let file_size = std::fs::metadata(path)
            .with_context(|| format!("Failed to get metadata for {path:?}"))?
            .len();

        let raw_size = Self::SIZE as u64;
        if file_size == raw_size {
            // This must be a raw signature, just read it as is.
            EcdsaRawSignature::read(&mut file)
        } else {
            // Let's try interpreting the file as ASN.1 DER.
            let mut data = Vec::<u8>::new();

            file.read_to_end(&mut data)
                .with_context(|| "Failed to read {path:?}")?;

            EcdsaRawSignature::from_der(&data).with_context(|| format!("Failed parsing {path:?}"))
        }
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<usize> {
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
        Ok(64)
    }

    pub fn to_vec(&self) -> Result<Vec<u8>> {
        let mut sig = Vec::new();
        self.write(&mut sig)?;
        Ok(sig)
    }

    pub fn is_empty(&self) -> bool {
        self.r.iter().all(|&v| v == 0) && self.s.iter().all(|&v| v == 0)
    }

    pub fn from_der_with_reverse(
        data: &[u8],
        reverse_byte_order: bool,
    ) -> Result<EcdsaRawSignature> {
        let sig = Signature::<NistP256>::from_der(data).with_context(|| "Failed to parse DER")?;

        // R and S are integers in big endian format. The size of the numbers is
        // not fixed, it could be 33 bytes in case the value has the top byte
        // top bit set, and a leading zero has to be added to keep the value
        // positive (50% chance), or it could be shorter than 32 bytes (1/256
        // chance). Need to get around these issues and convert into little
        // endian of exactly 32 bytes format expected by the firmware.
        let mut r: Vec<u8> = sig.r().to_bytes().to_vec();
        let mut s: Vec<u8> = sig.s().to_bytes().to_vec();

        // Convert to little endian format if requested.
        if reverse_byte_order {
            log::trace!("Reversing byte order of ECDSA sig");
            r.reverse();
            s.reverse();
        }

        // Pad with zeros if needed. This is required because the size of R and S
        // is not fixed in the ASN.1 DER format.
        r.resize(32, 0u8); // pad with zeros if needed.
        s.resize(32, 0u8); // pad with zeros if needed.

        Ok(EcdsaRawSignature { r, s })
    }

    pub fn from_der(data: &[u8]) -> Result<EcdsaRawSignature> {
        EcdsaRawSignature::from_der_with_reverse(data, true)
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
        self.key.verify_prehash(digest.as_ref(), &signature)?;
        Ok(())
    }
}

impl TryFrom<&EcdsaRawPublicKey> for EcdsaPublicKey {
    type Error = Error;
    fn try_from(v: &EcdsaRawPublicKey) -> Result<Self, Self::Error> {
        let mut x = v.x.clone();
        let mut y = v.y.clone();

        x.reverse();
        y.reverse();

        let key = VerifyingKey::from_encoded_point(&p256::EncodedPoint::from_affine_coordinates(
            &GenericArray::from(<[u8; 32]>::try_from(x.as_slice()).unwrap()),
            &GenericArray::from(<[u8; 32]>::try_from(y.as_slice()).unwrap()),
            false,
        ))
        .map_err(|e| Error::Other(anyhow!(e)))
        .context("Failed to create verifying key from raw public key")?;
        Ok(Self { key })
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

impl TryFrom<EcdsaPublicKey> for EcdsaRawPublicKey {
    type Error = Error;
    fn try_from(v: EcdsaPublicKey) -> Result<Self, Self::Error> {
        EcdsaRawPublicKey::try_from(&v)
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
