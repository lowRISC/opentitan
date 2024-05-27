// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sphincsplus_bindgen::crypto_sign_keypair;
use sphincsplus_bindgen::crypto_sign_seed_keypair;
use sphincsplus_bindgen::crypto_sign_signature;
use sphincsplus_bindgen::crypto_sign_verify;
use thiserror::Error;

// SPHINCS+ secret key byte length.
pub const SPX_SECRET_KEY_BYTES: usize = sphincsplus_bindgen::CRYPTO_SECRETKEYBYTES as usize;
pub const SPX_PUBLIC_KEY_BYTES: usize = sphincsplus_bindgen::CRYPTO_PUBLICKEYBYTES as usize;
pub const SPX_SIGNATURE_BYTES: usize = sphincsplus_bindgen::CRYPTO_BYTES as usize;
pub const SPX_SEED_BYTES: usize = sphincsplus_bindgen::CRYPTO_SEEDBYTES as usize;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpxPublicKey([u8; SPX_PUBLIC_KEY_BYTES]);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpxSecretKey([u8; SPX_SECRET_KEY_BYTES]);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpxSignature([u8; SPX_SIGNATURE_BYTES]);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpxSeed([u8; SPX_SEED_BYTES]);

#[derive(Debug, Error)]
pub enum SpxError {
    #[error("SPHINCS+ key generation failed with error code {0}")]
    KeyGen(i32),

    #[error("SPHINCS+ signature generation failed with error code {0}")]
    SigGen(i32),

    #[error("Unexpected signature length {0}")]
    BadSigLength(usize),

    #[error("Signature did not pass verification")]
    BadSignature,
}

impl SpxPublicKey {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl TryFrom<[u8; SPX_PUBLIC_KEY_BYTES]> for SpxPublicKey {
    type Error = SpxError;
    #[inline]
    fn try_from(buf: [u8; SPX_PUBLIC_KEY_BYTES]) -> Result<Self, SpxError> {
        Ok(SpxPublicKey(buf))
    }
}

impl SpxSecretKey {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl TryFrom<[u8; SPX_SECRET_KEY_BYTES]> for SpxSecretKey {
    type Error = SpxError;
    #[inline]
    fn try_from(buf: [u8; SPX_SECRET_KEY_BYTES]) -> Result<Self, SpxError> {
        Ok(SpxSecretKey(buf))
    }
}

impl SpxSignature {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl TryFrom<[u8; SPX_SIGNATURE_BYTES]> for SpxSignature {
    type Error = SpxError;
    #[inline]
    fn try_from(buf: [u8; SPX_SIGNATURE_BYTES]) -> Result<Self, SpxError> {
        Ok(SpxSignature(buf))
    }
}

impl SpxSeed {
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl TryFrom<[u8; SPX_SEED_BYTES]> for SpxSeed {
    type Error = SpxError;
    #[inline]
    fn try_from(buf: [u8; SPX_SEED_BYTES]) -> Result<Self, SpxError> {
        Ok(SpxSeed(buf))
    }
}

// Generate a new keypair from a seed.
pub fn spx_keypair_from_seed(seed: &SpxSeed) -> Result<(SpxPublicKey, SpxSecretKey), SpxError> {
    let mut pk = [0u8; SPX_PUBLIC_KEY_BYTES];
    let mut sk = [0u8; SPX_SECRET_KEY_BYTES];
    let err_code =
        // SAFETY: the buffers here are all fixed-length arrays of the size expected by the C code.
        unsafe { crypto_sign_seed_keypair(pk.as_mut_ptr(), sk.as_mut_ptr(), seed.0.as_ptr()) };
    if err_code != 0 {
        return Err(SpxError::KeyGen(err_code));
    }
    Ok((SpxPublicKey(pk), SpxSecretKey(sk)))
}

// Generate a new random keypair.
pub fn spx_keypair_generate() -> Result<(SpxPublicKey, SpxSecretKey), SpxError> {
    let mut pk = [0u8; SPX_PUBLIC_KEY_BYTES];
    let mut sk = [0u8; SPX_SECRET_KEY_BYTES];
    let err_code =
        // SAFETY: the buffers here are all fixed-length arrays of the size expected by the C code.
        unsafe { crypto_sign_keypair(pk.as_mut_ptr(), sk.as_mut_ptr()) };
    if err_code != 0 {
        return Err(SpxError::KeyGen(err_code));
    }
    Ok((SpxPublicKey(pk), SpxSecretKey(sk)))
}

// Generate a detached signature for the message using the secret key.
pub fn spx_sign(sk: &SpxSecretKey, msg: &[u8]) -> Result<SpxSignature, SpxError> {
    let mut sig = [0u8; SPX_SIGNATURE_BYTES];
    let mut sig_bytes_written = 0;
    let err_code =
        // SAFETY: the signature and secret key buffers here are fixed-length arrays of the size
        // expected by the C code, and the message buffer is passed along with its length. The
        // signature is always the same length, but the implementation returns the number of bytes
        // written as part of the result; we check this value later in the non-error case against
        // the expected length.
        unsafe {
        crypto_sign_signature(
            sig.as_mut_ptr(),
            &mut sig_bytes_written,
            msg.as_ptr(),
            msg.len(),
            sk.0.as_ptr(),
        )
    };
    if err_code != 0 {
        return Err(SpxError::SigGen(err_code));
    }
    if sig_bytes_written != sig.len() {
        return Err(SpxError::BadSigLength(sig_bytes_written));
    }
    Ok(SpxSignature(sig))
}

// Verify a detached signature and return true if the signature is valid.
pub fn spx_verify(pk: &SpxPublicKey, sig: &SpxSignature, msg: &[u8]) -> Result<(), SpxError> {
    let err_code =
        // SAFETY: the signature and public key buffers here are fixed-length arrays of the size
        // expected by the C code, and the message buffer is passed along with its length.
        unsafe {
        crypto_sign_verify(
            sig.0.as_ptr(),
            sig.0.len(),
            msg.as_ptr(),
            msg.len(),
            pk.0.as_ptr(),
        )
    };
    if err_code != 0 {
        return Err(SpxError::BadSignature);
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn keypair_different_seeds_test() {
        // Generate keypairs from two different seeds and check that the values are not equal.
        let seed1 = SpxSeed([255u8; SPX_SEED_BYTES]);
        let (pk1, sk1) = spx_keypair_from_seed(&seed1).unwrap();
        let seed2 = SpxSeed([0u8; SPX_SEED_BYTES]);
        let (pk2, sk2) = spx_keypair_from_seed(&seed2).unwrap();
        assert_ne!(pk1, pk2);
        assert_ne!(sk1, sk2);
    }

    #[test]
    fn keypair_same_seed_test() {
        // Generate keypairs from the same seed and check that the values are equal.
        let seed = SpxSeed([255u8; SPX_SEED_BYTES]);
        let (pk1, sk1) = spx_keypair_from_seed(&seed).unwrap();
        let (pk2, sk2) = spx_keypair_from_seed(&seed).unwrap();
        assert_eq!(pk1, pk2);
        assert_eq!(sk1, sk2);
    }

    #[test]
    fn random_keypair_test() {
        // Generate two random keypairs and check that they are not equal.
        let (pk1, sk1) = spx_keypair_generate().unwrap();
        let (pk2, sk2) = spx_keypair_generate().unwrap();
        assert_ne!(pk1, pk2);
        assert_ne!(sk1, sk2);
    }

    #[test]
    fn sign_verify_test() {
        // Check that a generated signature passes verification.
        let (pk, sk) = spx_keypair_generate().unwrap();
        let msg = [255u8; 100];
        let mut sig = spx_sign(&sk, &msg).unwrap();
        assert!(spx_verify(&pk, &sig, &msg).is_ok());

        // Check that manipulating the signature causes it to fail verification.
        sig.0[0] ^= 0xff;
        let verification_result = spx_verify(&pk, &sig, &msg);
        assert!(verification_result.is_err());
        assert_eq!(
            verification_result.unwrap_err().to_string(),
            SpxError::BadSignature.to_string()
        );
    }
}
