// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::{DecodeKey, EncodeKey, SphincsPlus, SpxError};
use pem_rfc7468::LineEnding;
use std::borrow::Cow;
use std::fmt;
use std::str::FromStr;
use strum::{Display, EnumString};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SpxPublicKey {
    algorithm: SphincsPlus,
    key: Vec<u8>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct SpxSecretKey {
    algorithm: SphincsPlus,
    key: Vec<u8>,
}

impl fmt::Debug for SpxSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpxSecretKey")
            .field("algorithm", &self.algorithm)
            .field("key", &"REDACTED")
            .finish()
    }
}

#[derive(Default, Debug, Clone, Copy, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum SpxDomain {
    None,
    #[default]
    Pure,
    PreHashedSha256,
}

impl SpxDomain {
    #[rustfmt::skip]
    const SHA256_DOMAIN: [u8; 13] = [
        // Domain separator.
        1u8, 0u8,
        // Sha256 OID: 2.16.840.1.101.3.4.2.1.
        0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
    ];
    pub fn prepare<'a>(&self, message: &'a [u8]) -> Cow<'a, [u8]> {
        match self {
            Self::None => message.into(),
            Self::Pure => [&[0u8, 0u8], message].concat().into(),
            Self::PreHashedSha256 => [&Self::SHA256_DOMAIN, message].concat().into(),
        }
    }
}

impl SpxSecretKey {
    /// Creates a new SPHINCS+ keypair for the given algorithm.
    pub fn new_keypair(algorithm: SphincsPlus) -> Result<(Self, SpxPublicKey), SpxError> {
        let (pk, sk) = algorithm.keypair_generate()?;
        let pk = SpxPublicKey { algorithm, key: pk };
        let sk = SpxSecretKey { algorithm, key: sk };
        Ok((sk, pk))
    }

    /// Creates a new SPHINCS+ keypair from a seed for the given algorithm.
    pub fn keypair_from_seed(
        algorithm: SphincsPlus,
        seed: &[u8],
    ) -> Result<(Self, SpxPublicKey), SpxError> {
        let (pk, sk) = algorithm.keypair_from_seed(seed)?;
        let pk = SpxPublicKey { algorithm, key: pk };
        let sk = SpxSecretKey { algorithm, key: sk };
        Ok((sk, pk))
    }

    /// Creates a SPHINCS+ secret key from raw bytes.
    pub fn from_bytes(algorithm: SphincsPlus, bytes: &[u8]) -> Result<Self, SpxError> {
        if algorithm.secret_key_len() != bytes.len() {
            return Err(SpxError::BadKeyLength(bytes.len()));
        }
        Ok(Self {
            algorithm,
            key: bytes.to_vec(),
        })
    }

    /// Returns the algorithm associated with this key.
    pub fn algorithm(&self) -> SphincsPlus {
        self.algorithm
    }

    /// Returns the raw key bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.key.as_slice()
    }

    /// Signs the given message with the key.
    pub fn sign(&self, domain: SpxDomain, msg: &[u8]) -> Result<Vec<u8>, SpxError> {
        let msg = domain.prepare(msg);
        self.algorithm.sign(&self.key, &msg)
    }
}

impl DecodeKey for SpxSecretKey {
    /// Decodes a SPHINCS+ secret key from a PEM encoded string.
    fn from_pem(s: &str) -> Result<Self, SpxError> {
        let (label, mut key) = pem_rfc7468::decode_vec(s.as_bytes()).map_err(SpxError::Pem)?;
        let (algorithm, _) = label
            .split_once(' ')
            .ok_or_else(|| SpxError::ParseError(format!("failed to parse label: {label:?}")))?;
        if !label.contains("PRIVATE KEY") {
            return Err(SpxError::ParseError(format!(
                "not a private key: {label:?}"
            )));
        }
        if !algorithm.starts_with("RAW:") {
            return Err(SpxError::ParseError(format!("not a RAW key: {label:?}")));
        }
        let algorithm = algorithm[4..].replace('_', "-");
        let algorithm = SphincsPlus::from_str(&algorithm).map_err(SpxError::Strum)?;
        if key.len() == algorithm.public_key_len() + algorithm.secret_key_len() {
            // Older versions of our tooling would save the private key as PubKey || SecretKey.
            // It appears we were unaware that sphincsplus secret keys _already_ contain a copy
            // of the public key.
            // We compensate here by discarding the copy of the PubKey at the beginning of
            // the array of bytes.
            key = key.split_off(algorithm.public_key_len());
        }
        if key.len() != algorithm.secret_key_len() {
            return Err(SpxError::ParseError(format!(
                "bad private key length for {algorithm}; expected {} but got {}",
                algorithm.secret_key_len(),
                key.len()
            )));
        }
        Ok(Self { algorithm, key })
    }
}

impl EncodeKey for SpxSecretKey {
    /// Encodes the SPHINCS+ secret key as a PEM encoded string.
    fn to_pem(&self) -> Result<String, SpxError> {
        // RFC7468 permits hyphen-minus in the label as long as it isn't the
        // first character.  The pem_rfc7468 crate does not.
        let algorithm = self.algorithm.to_string().replace('-', "_");
        pem_rfc7468::encode_string(
            &format!("RAW:{algorithm} PRIVATE KEY"),
            LineEnding::default(),
            &self.key,
        )
        .map_err(SpxError::Pem)
    }
}

impl SpxPublicKey {
    /// Creates a SPHINCS+ public key from raw bytes.
    pub fn from_bytes(algorithm: SphincsPlus, bytes: &[u8]) -> Result<Self, SpxError> {
        if algorithm.public_key_len() != bytes.len() {
            return Err(SpxError::BadKeyLength(bytes.len()));
        }
        Ok(Self {
            algorithm,
            key: bytes.to_vec(),
        })
    }

    /// Returns the algorithm associated with this key.
    pub fn algorithm(&self) -> SphincsPlus {
        self.algorithm
    }

    /// Returns the raw key bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.key.as_slice()
    }

    /// Verifies the signature and message with the public key.
    pub fn verify(&self, domain: SpxDomain, signature: &[u8], msg: &[u8]) -> Result<(), SpxError> {
        let msg = domain.prepare(msg);
        self.algorithm.verify(&self.key, signature, &msg)
    }
}

impl DecodeKey for SpxPublicKey {
    /// Decodes a SPHINCS+ public key from a PEM encoded string.
    fn from_pem(s: &str) -> Result<Self, SpxError> {
        let (label, key) = pem_rfc7468::decode_vec(s.as_bytes()).map_err(SpxError::Pem)?;
        let (algorithm, _) = label
            .split_once(' ')
            .ok_or_else(|| SpxError::ParseError(format!("failed to parse label: {label:?}")))?;
        if !label.contains("PUBLIC KEY") {
            if label.contains("PRIVATE KEY") {
                // Decode the private key and convert to public key.
                return SpxSecretKey::from_pem(s).map(|ref k| k.into());
            }
            return Err(SpxError::ParseError(format!("not a public key: {label:?}")));
        }
        if !algorithm.starts_with("RAW:") {
            return Err(SpxError::ParseError(format!("not a RAW key: {label:?}")));
        }
        let algorithm = algorithm[4..].replace('_', "-");
        let algorithm = SphincsPlus::from_str(&algorithm).map_err(SpxError::Strum)?;
        if key.len() != algorithm.public_key_len() {
            return Err(SpxError::ParseError(format!(
                "bad public key length for {algorithm}; expected {} but got {}",
                algorithm.public_key_len(),
                key.len()
            )));
        }
        Ok(Self { algorithm, key })
    }
}

impl EncodeKey for SpxPublicKey {
    /// Encodes the SPHINCS+ public key as a PEM encoded string.
    fn to_pem(&self) -> Result<String, SpxError> {
        // RFC7468 permits hyphen-minus in the label as long as it isn't the
        // first character.  The pem_rfc7468 crate does not.
        let algorithm = self.algorithm.to_string().replace('-', "_");
        pem_rfc7468::encode_string(
            &format!("RAW:{algorithm} PUBLIC KEY"),
            LineEnding::default(),
            &self.key,
        )
        .map_err(SpxError::Pem)
    }
}

impl From<&SpxSecretKey> for SpxPublicKey {
    /// Creates a public key from a secret key object.
    fn from(sk: &SpxSecretKey) -> Self {
        // By convention, the second half of the secret key is the public key.
        let offset = sk.algorithm.secret_key_len() / 2;
        Self {
            algorithm: sk.algorithm,
            key: sk.key[offset..].to_vec(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn key_encoding() -> Result<(), SpxError> {
        let (sk, pk) = SpxSecretKey::new_keypair(SphincsPlus::Shake128sSimple)?;

        // Secret key encode/decode.
        let secret_pem = sk.to_pem()?;
        let xk = SpxSecretKey::from_pem(&secret_pem)?;
        assert_eq!(sk, xk);

        // Public key encode/decode.
        let public_pem = pk.to_pem()?;
        let xk = SpxPublicKey::from_pem(&public_pem)?;
        assert_eq!(pk, xk);

        // Public key decode from private key.
        let xk = SpxPublicKey::from_pem(&secret_pem)?;
        assert_eq!(pk, xk);

        // Error conditions for confusing secret/public.
        assert!(SpxSecretKey::from_pem(&public_pem).is_err());
        Ok(())
    }

    #[test]
    fn secret_key_to_public_key() -> Result<(), SpxError> {
        let (sk, pk) = SpxSecretKey::new_keypair(SphincsPlus::Sha2128sSimple)?;
        // Convert secret key to public key.
        let xk = SpxPublicKey::from(&sk);
        assert_eq!(pk, xk);
        Ok(())
    }

    #[test]
    fn sign_verify() -> Result<(), SpxError> {
        let (sk, pk) = SpxSecretKey::new_keypair(SphincsPlus::Sha2128sSimple)?;
        let msg = b"The quick brown fox jumped over the lazy dog.";

        // Sign and verify.
        let mut sig = sk.sign(SpxDomain::Pure, msg)?;
        assert!(pk.verify(SpxDomain::Pure, &sig, msg).is_ok());

        // Verify fail with bad signature.
        sig[0] ^= 0xFF;
        let err = pk.verify(SpxDomain::Pure, &sig, msg).unwrap_err();
        assert!(matches!(err, SpxError::BadSignature));
        Ok(())
    }

    #[test]
    fn sign_verify_prehash() -> Result<(), SpxError> {
        // SHA256('Test message')
        let digest = [
            0xc0, 0x71, 0x9e, 0x9a, 0x8d, 0x5d, 0x83, 0x8d, 0x86, 0x1d, 0xc6, 0xf6, 0x75, 0xc8,
            0x99, 0xd2, 0xb3, 0x09, 0xa3, 0xa6, 0x5b, 0xb9, 0xfe, 0x6b, 0x11, 0xe5, 0xaf, 0xcb,
            0xf9, 0xa2, 0xc0, 0xb1,
        ];

        let (sk, pk) = SpxSecretKey::new_keypair(SphincsPlus::Sha2128sSimple)?;

        // Sign and verify.
        let sig = sk.sign(SpxDomain::PreHashedSha256, &digest)?;
        assert!(pk.verify(SpxDomain::PreHashedSha256, &sig, &digest).is_ok());

        // Independently construct the message with the prehash domain separator
        // and SHA256 OID to verify the pre-hash preparation performed by the
        // signing fuction yields the correct result.
        let domain_sep = [1, 0];
        let sha256_oid = [
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
        ];
        let msg = [domain_sep.as_slice(), &sha256_oid, &digest].concat();
        assert!(pk.verify(SpxDomain::None, &sig, &msg).is_ok());
        Ok(())
    }
}
