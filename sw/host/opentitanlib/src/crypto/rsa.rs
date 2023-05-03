// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use num_bigint_dig::{traits::ModInverse, BigInt, BigUint, Sign::Minus};
use rand::rngs::OsRng;
use rsa::pkcs1::{DecodeRsaPublicKey, EncodeRsaPublicKey};
use rsa::pkcs8::{DecodePrivateKey, EncodePrivateKey};
use rsa::{pkcs1v15::Pkcs1v15Sign, PublicKey as _, PublicKeyParts};
use sha2::{Digest, Sha256};
use signature::{DigestSigner, DigestVerifier, Keypair, Signer, Verifier};
use std::io::{Read, Write};
use std::ops::Shl;
use std::path::PathBuf;

use crate::util::bigint::fixed_size_bigint;
use crate::util::file::{FileReadable, FileWritable, FromReader, PemSerilizable, ToWriter};

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
fn validate_key(key: &impl rsa::PublicKeyParts) -> Result<()> {
    if key.n().bits() != MODULUS_BIT_LEN || key.e() != &BigUint::from(65537u32) {
        bail!("Invalid public key")
    } else {
        Ok(())
    }
}

/// RSA Public Key used in OpenTitan signing operations.
///
/// This is a wrapper for handling RSA public keys as they're used in OpenTitan images.
#[derive(Clone, Debug)]
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
            )?,
        })
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
            .ok_or(anyhow!("Failed to compute n0_inv"))?;
        Ok(N0Inv::from_le_bytes(n0_inv.to_bytes_le())?)
    }

    /// The montgomery parameter RR.
    pub fn rr(&self) -> RR {
        let rr = BigUint::from(1u8).shl(2 * self.bit_length()) % self.key.n();
        // `rr` < `n`, so `rr` will always fit in `RR` and thus `unwrap()` here is safe.
        RR::from_le_bytes(rr.to_bytes_le()).unwrap()
    }

    /// The bit-length of this key.
    pub fn bit_length(&self) -> usize {
        self.key.n().bits()
    }
}

impl DigestVerifier<sha2::Sha256, Signature> for RsaPublicKey {
    fn verify_digest(
        &self,
        digest: sha2::Sha256,
        signature: &Signature,
    ) -> std::result::Result<(), signature::Error> {
        self.key.verify(
            Pkcs1v15Sign::new::<Sha256>(),
            &digest.finalize(),
            signature.to_be_bytes().as_slice(),
        )?;
        Ok(())
    }
}

impl Verifier<Signature> for RsaPublicKey {
    fn verify(
        &self,
        msg: &[u8],
        signature: &Signature,
    ) -> std::result::Result<(), signature::Error> {
        self.key.verify(
            Pkcs1v15Sign::new::<Sha256>(),
            msg,
            signature.to_be_bytes().as_slice(),
        )?;
        Ok(())
    }
}

impl FileReadable for RsaPublicKey {
    fn read_from_file<P: Into<PathBuf>>(file: P) -> Result<Self> {
        // Construct a new public key from a PKCS1 encoded DER file.
        let key = rsa::RsaPublicKey::read_pkcs1_der_file(file.into())?;
        validate_key(&key)?;
        Ok(Self { key })
    }
}

impl FileWritable for RsaPublicKey {
    fn write_to_file<P: Into<PathBuf>>(&self, file: P) -> Result<()> {
        self.key.write_pkcs1_der_file(file.into())?;
        Ok(())
    }
}

/// RSA Private Key used in OpenTitan signing operations.
///
/// This is a wrapper for handling RSA priavate keys as they're used in OpenTitan images.
#[derive(Clone, Debug)]
pub struct RsaPrivateKey {
    key: rsa::RsaPrivateKey,
}

impl RsaPrivateKey {
    /// Construct a new 3072-bit private key with e = 65537.
    pub fn new() -> Result<Self> {
        let mut rng = OsRng;
        Ok(Self {
            key: rsa::RsaPrivateKey::new_with_exp(&mut rng, 3072, &BigUint::from(65537u32))?,
        })
    }
}

impl FileReadable for RsaPrivateKey {
    fn read_from_file<P: Into<PathBuf>>(file: P) -> Result<Self> {
        // Construct a new private key from a PKCS8 encoded DER file.
        let key = rsa::RsaPrivateKey::read_pkcs8_der_file(file.into())?;
        validate_key(&key)?;
        Ok(Self { key })
    }
}

impl FileWritable for RsaPrivateKey {
    fn write_to_file<P: Into<PathBuf>>(&self, file: P) -> Result<()> {
        // Write private key to a PKCS8 encoded DER file.
        self.key.write_pkcs8_der_file(file.into())?;
        Ok(())
    }
}

impl Keypair for RsaPrivateKey {
    type VerifyingKey = RsaPublicKey;

    fn verifying_key(&self) -> Self::VerifyingKey {
        RsaPublicKey {
            key: self.key.to_public_key(),
        }
    }
}

impl DigestSigner<sha2::Sha256, Signature> for RsaPrivateKey {
    fn try_sign_digest(
        &self,
        digest: sha2::Sha256,
    ) -> std::result::Result<Signature, signature::Error> {
        let signature = self
            .key
            .sign(Pkcs1v15Sign::new::<Sha256>(), &digest.finalize())?;
        Ok(Signature::from_be_bytes(signature).unwrap())
    }
}

impl Signer<Signature> for RsaPrivateKey {
    fn try_sign(&self, msg: &[u8]) -> std::result::Result<Signature, signature::Error> {
        let signature = self.key.sign(Pkcs1v15Sign::new::<Sha256>(), msg)?;
        Ok(Signature::from_be_bytes(signature).unwrap())
    }
}

impl FromReader for Signature {
    fn from_reader(mut r: impl Read) -> Result<Self> {
        let mut buf = Vec::<u8>::new();
        r.read_to_end(&mut buf)?;
        Ok(Signature::from_le_bytes(buf.as_slice())?)
    }
}

impl ToWriter for Signature {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(self.to_le_bytes().as_mut_slice())?;
        Ok(())
    }
}

impl PemSerilizable for Signature {
    fn label() -> &'static str {
        "RSA Signature"
    }
}
