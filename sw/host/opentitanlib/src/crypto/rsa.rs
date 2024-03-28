// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, ensure, Context, Result};
use num_bigint_dig::{traits::ModInverse, BigInt, BigUint, Sign::Minus};
use rand::rngs::OsRng;
use rsa::pkcs1::{DecodeRsaPublicKey, EncodeRsaPublicKey};
use rsa::pkcs1v15::Pkcs1v15Sign;
use rsa::pkcs8::{DecodePrivateKey, EncodePrivateKey};
use rsa::traits::PublicKeyParts;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use sha2::Sha256;
use std::fs::File;
use std::io::{Read, Write};
use std::ops::Deref;
use std::ops::Shl;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use super::Error;
use crate::crypto::sha256::Sha256Digest;
use crate::util::bigint::fixed_size_bigint;

const MODULUS_BIT_LEN: usize = 3072;
const EXPONENT_BIT_LEN: usize = 17;
const SIGNATURE_BIT_LEN: usize = 3072;
const RR_BIT_LEN: usize = 3072;
const OTBN_BITS: usize = 256;

fixed_size_bigint!(Modulus, MODULUS_BIT_LEN);
fixed_size_bigint!(Exponent, EXPONENT_BIT_LEN);
fixed_size_bigint!(Signature, at_most SIGNATURE_BIT_LEN);
fixed_size_bigint!(RR, at_most RR_BIT_LEN);
fixed_size_bigint!(N0Inv, at_most OTBN_BITS);

/// Ensure the components of `key` have the correct bit length.
fn validate_key(key: &impl PublicKeyParts) -> Result<()> {
    if key.n().bits() != MODULUS_BIT_LEN || key.e() != &BigUint::from(65537u32) {
        bail!(Error::InvalidPublicKey(anyhow!("bad modulus or exponent")));
    } else {
        Ok(())
    }
}

/// RSA Public Key used in OpenTitan signing operations.
///
/// This is a wrapper for handling RSA public keys as they're used in OpenTitan images.
#[derive(Debug)]
pub struct RsaPublicKey {
    key: rsa::RsaPublicKey,
}

impl RsaPublicKey {
    /// Construct a new public key with modulus = n and e = 65537.
    pub fn new(n: Modulus) -> Result<RsaPublicKey> {
        Ok(RsaPublicKey {
            key: rsa::RsaPublicKey::new(
                BigUint::from_bytes_le(n.to_le_bytes().as_slice()),
                BigUint::from(65537u32),
            )
            .map_err(|e| Error::InvalidPublicKey(anyhow!(e)))?,
        })
    }

    /// Construct a new public key from a PKCS1 encoded DER file.
    pub fn from_pkcs1_der_file<P: Into<PathBuf>>(der_file: P) -> Result<RsaPublicKey> {
        let der_file = der_file.into();
        match rsa::RsaPublicKey::read_pkcs1_der_file(&der_file) {
            Ok(key) => {
                validate_key(&key)?;
                Ok(Self { key })
            }
            Err(err) => bail!(Error::InvalidDerFile {
                der: der_file,
                source: anyhow!(err),
            }),
        }
    }

    /// Write public key to a PKCS1 encoded DER file.
    pub fn to_pkcs1_der_file<P: Into<PathBuf>>(&self, der_file: P) -> Result<()> {
        let der_file = der_file.into();
        self.key
            .write_pkcs1_der_file(&der_file)
            .map_err(|e| Error::WriteFailed {
                file: der_file.to_owned(),
                source: anyhow!(e),
            })?;
        Ok(())
    }

    /// Extract the public key components from a given private key.
    pub fn from_private_key(private_key: &RsaPrivateKey) -> Self {
        Self {
            key: rsa::RsaPublicKey::from(&private_key.key),
        }
    }

    /// Bit length for this key.
    pub fn modulus_num_bits(&self) -> usize {
        self.key.n().bits()
    }

    /// Modulus for this key.
    pub fn modulus(&self) -> Modulus {
        // All RSA keys have their bit length checked so `unwrap()` here is safe.
        Modulus::from_le_bytes(self.key.n().to_bytes_le()).unwrap()
    }

    /// Public exponent for this key.
    pub fn exponent(&self) -> Exponent {
        // All RSA keys have their bit length checked so `unwrap()` here is safe.
        Exponent::from_le_bytes(self.key.e().to_bytes_le()).unwrap()
    }

    /// Computes the OTBN montgomery parameter: -1 / n\[0\] mod 2^256.
    pub fn n0_inv(&self) -> Result<N0Inv> {
        let base = BigInt::from(1u8) << OTBN_BITS;
        let n_neg = BigInt::from_biguint(Minus, self.key.n().to_owned());
        let n0_inv = n_neg
            .mod_inverse(&base)
            .and_then(|v| v.to_biguint())
            .ok_or(Error::KeyComponentComputeFailed)?;
        Ok(N0Inv::from_le_bytes(n0_inv.to_bytes_le())?)
    }

    /// The montgomery parameter RR.
    pub fn rr(&self) -> RR {
        let rr = BigUint::from(1u8).shl(2 * self.modulus_num_bits()) % self.key.n();
        // `rr` < `n`, so `rr` will always fit in `RR` and thus `unwrap()` here is safe.
        RR::from_le_bytes(rr.to_bytes_le()).unwrap()
    }

    /// Verify a `signature` is valid for a given `digest` under this key.
    pub fn verify(&self, digest: &Sha256Digest, signature: &Signature) -> Result<()> {
        self.key
            .verify(
                Pkcs1v15Sign::new::<Sha256>(),
                digest.to_be_bytes().as_slice(),
                signature.to_be_bytes().as_slice(),
            )
            .map_err(|e| anyhow!(Error::VerifyFailed(anyhow!(e))))
    }
}

/// RSA Private Key used in OpenTitan signing operations.
///
/// This is a wrapper for handling RSA priavate keys as they're used in OpenTitan images.
#[derive(Debug, Clone)]
pub struct RsaPrivateKey {
    key: rsa::RsaPrivateKey,
}

impl RsaPrivateKey {
    /// Construct a new 3072-bit private key with e = 65537.
    pub fn new() -> Result<Self> {
        let mut rng = OsRng;
        Ok(Self {
            key: rsa::RsaPrivateKey::new_with_exp(&mut rng, 3072, &BigUint::from(65537u32))
                .map_err(|e| Error::GenerateFailed(anyhow!(e)))?,
        })
    }

    /// Construct a new private key from a PKCS8 encoded DER file.
    pub fn from_pkcs8_der_file<P: Into<PathBuf>>(der_file: P) -> Result<Self> {
        let der_file = der_file.into();
        match rsa::RsaPrivateKey::read_pkcs8_der_file(&der_file) {
            Ok(key) => {
                validate_key(&key)?;
                Ok(Self { key })
            }
            Err(err) => bail!(Error::InvalidDerFile {
                der: der_file,
                source: anyhow!(err),
            }),
        }
    }

    /// Write private key to a PKCS8 encoded DER file.
    pub fn to_pkcs8_der_file<P: Into<PathBuf>>(&self, der_file: P) -> Result<()> {
        let der_file = der_file.into();
        self.key
            .write_pkcs8_der_file(&der_file)
            .map_err(|e| Error::WriteFailed {
                file: der_file,
                source: anyhow!(e),
            })?;
        Ok(())
    }

    /// Signs a SHA256 `digest` using PKCS1v15 padding scheme.
    pub fn sign(&self, digest: &Sha256Digest) -> Result<Signature> {
        let signature = self
            .key
            .sign(Pkcs1v15Sign::new::<Sha256>(), &digest.to_be_bytes())
            .map_err(|e| Error::SignFailed(anyhow!(e)))?;
        Ok(Signature::from_be_bytes(signature)?)
    }
}

impl Signature {
    /// Creates an `Signature` from a given input file.
    pub fn read_from_file(path: &Path) -> Result<Signature> {
        let err = |e: std::io::Error| Error::ReadFailed {
            file: path.to_owned(),
            source: anyhow!(e),
        };
        let mut file = File::open(path).map_err(err)?;
        let mut buf = Vec::<u8>::new();
        file.read_to_end(&mut buf).map_err(err)?;
        Ok(Signature::from_le_bytes(buf.as_slice())?)
    }

    /// Write out the `Signature` to a file at the given `path`.
    pub fn write_to_file(&self, path: &Path) -> Result<()> {
        let err = |e: std::io::Error| Error::WriteFailed {
            file: path.to_owned(),
            source: anyhow!(e),
        };
        let mut file = File::create(path).map_err(err)?;
        file.write_all(self.to_le_bytes().as_mut_slice())
            .map_err(err)?;
        Ok(())
    }
}

impl Deref for RsaPublicKey {
    type Target = rsa::RsaPublicKey;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

impl Deref for RsaPrivateKey {
    type Target = rsa::RsaPrivateKey;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct RsaRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub modulus: Vec<u8>,
    pub n0_inv: Vec<u8>,
}

impl Default for RsaRawPublicKey {
    fn default() -> Self {
        Self {
            modulus: vec![0; 384],
            n0_inv: vec![0; 32],
        }
    }
}

impl TryFrom<&RsaPublicKey> for RsaRawPublicKey {
    type Error = Error;
    fn try_from(v: &RsaPublicKey) -> Result<Self, Self::Error> {
        Ok(Self {
            modulus: v.modulus().to_le_bytes().to_vec(),
            n0_inv: v.n0_inv().map_err(Error::Other)?.to_le_bytes().to_vec(),
        })
    }
}

impl FromStr for RsaRawPublicKey {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let key = RsaPublicKey::from_pkcs1_der_file(s)
            .with_context(|| format!("Failed to load {s}"))
            .map_err(Error::Other)?;
        RsaRawPublicKey::try_from(&key)
    }
}

impl RsaRawPublicKey {
    pub const SIZE: usize = 384 + 32;
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut key = Self::default();
        src.read_exact(&mut key.modulus)?;
        src.read_exact(&mut key.n0_inv)?;
        Ok(key)
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.modulus.len() == 384,
            Error::InvalidPublicKey(anyhow!("bad modulus length: {}", self.modulus.len()))
        );
        ensure!(
            self.n0_inv.len() == 32,
            Error::InvalidPublicKey(anyhow!("bad n0_inv length: {}", self.n0_inv.len()))
        );
        dest.write_all(&self.modulus)?;
        dest.write_all(&self.n0_inv)?;
        Ok(())
    }
}
