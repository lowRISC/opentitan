// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::{DecodeKey, EncodeKey, MldsaError, MldsaParameterSet};
use ml_dsa::Seed;
use ml_dsa::common::getrandom;
use pkcs8::der::asn1::{BitStringRef, ContextSpecific, OctetStringRef};
use pkcs8::der::{AnyRef, Decode, Encode, SliceReader, Tag, TagMode, TagNumber, Tagged, pem};
use pkcs8::{AlgorithmIdentifierRef, PrivateKeyInfoRef, SubjectPublicKeyInfoRef};
use std::fmt;
use zeroize::Zeroizing;

/// Tag number of the `seed` alternative of ML-DSA-PrivateKey.
const SEED_TAG_NUMBER: TagNumber = TagNumber(0);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MldsaPublicKey {
    parameter_set: MldsaParameterSet,
    key: Vec<u8>,
}

/// An ML-DSA private key, stored as the seed from which the key pair is derived.
#[derive(Clone, PartialEq, Eq)]
pub struct MldsaSecretKey {
    parameter_set: MldsaParameterSet,
    seed: Zeroizing<Seed>,
}

impl fmt::Debug for MldsaSecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MldsaSecretKey")
            .field("parameter_set", &self.parameter_set)
            .field("seed", &"REDACTED")
            .finish()
    }
}

impl From<MldsaParameterSet> for AlgorithmIdentifierRef<'static> {
    /// Returns the algorithm identifier of a parameter set.
    fn from(parameter_set: MldsaParameterSet) -> Self {
        Self {
            oid: parameter_set.oid(),
            parameters: None,
        }
    }
}

impl TryFrom<&AlgorithmIdentifierRef<'_>> for MldsaParameterSet {
    type Error = MldsaError;

    /// Returns the parameter set identified by an algorithm identifier.
    fn try_from(algorithm: &AlgorithmIdentifierRef<'_>) -> Result<Self, MldsaError> {
        match MldsaParameterSet::from_oid(algorithm.oid) {
            Some(p) if algorithm.parameters.is_none() => Ok(p),
            _ => Err(MldsaError::ParseError(format!(
                "not an ML-DSA key: {}",
                algorithm.oid
            ))),
        }
    }
}

fn decode_pem(pem: &[u8], label: &str) -> Result<Zeroizing<Vec<u8>>, MldsaError> {
    let (actual, der) = pem::decode_vec(pem)?;
    let der = Zeroizing::new(der);
    if actual != label {
        return Err(MldsaError::ParseError(format!(
            "expected a {label:?} PEM block but got {actual:?}"
        )));
    }
    Ok(der)
}

fn encode_pem(der: &[u8], label: &str) -> Result<String, MldsaError> {
    Ok(pem::encode_string(label, pem::LineEnding::default(), der)?)
}

impl MldsaSecretKey {
    /// Generates a new ML-DSA private key for the given parameter set.
    pub fn generate(parameter_set: MldsaParameterSet) -> Result<Self, MldsaError> {
        let mut seed = Zeroizing::new(Seed::default());
        getrandom::fill(seed.as_mut_slice())?;
        Ok(Self {
            parameter_set,
            seed,
        })
    }

    /// Returns the parameter set of this key.
    pub fn parameter_set(&self) -> MldsaParameterSet {
        self.parameter_set
    }

    /// Derives the public key of this private key.
    pub fn public_key(&self) -> MldsaPublicKey {
        MldsaPublicKey {
            parameter_set: self.parameter_set,
            key: self.parameter_set.public_key(&self.seed),
        }
    }

    /// Signs the given message with the key under the given context string (pure mode).
    pub fn sign(&self, context: &[u8], msg: &[u8]) -> Result<Vec<u8>, MldsaError> {
        self.parameter_set.sign(&self.seed, context, msg)
    }

    /// Decodes the seed from an ML-DSA-PrivateKey, which is either the seed,
    /// the expanded key or both.
    fn decode_seed(
        parameter_set: MldsaParameterSet,
        private_key: &[u8],
    ) -> Result<Zeroizing<Seed>, MldsaError> {
        let choice = AnyRef::from_der(private_key)?;
        let seed = match choice.tag() {
            Tag::ContextSpecific {
                constructed: false,
                number: SEED_TAG_NUMBER,
            } => choice.value(),
            Tag::Sequence => {
                let (seed, expanded) = choice.sequence(|r: &mut SliceReader<'_>| {
                    Ok::<_, MldsaError>((
                        <&OctetStringRef>::decode(r)?.as_bytes(),
                        <&OctetStringRef>::decode(r)?.as_bytes(),
                    ))
                })?;
                let seed =
                    Seed::try_from(seed).map_err(|_| MldsaError::BadKeyLength(seed.len()))?;
                if parameter_set.expanded_key(&seed).as_slice() != expanded {
                    return Err(MldsaError::ParseError(
                        "expanded private key does not match the seed".into(),
                    ));
                }
                return Ok(Zeroizing::new(seed));
            }
            Tag::OctetString => {
                return Err(MldsaError::ParseError(
                    "expanded-only ML-DSA private keys are not supported".into(),
                ));
            }
            tag => {
                return Err(MldsaError::ParseError(format!(
                    "unexpected ML-DSA private key encoding {tag}"
                )));
            }
        };
        Ok(Zeroizing::new(
            Seed::try_from(seed).map_err(|_| MldsaError::BadKeyLength(seed.len()))?,
        ))
    }
}

impl DecodeKey for MldsaSecretKey {
    /// Decodes an ML-DSA private key from a DER encoded PKCS#8v1
    /// (PrivateKeyInfo) or PKCS#8v2 (OneAsymmetricKey).
    fn from_der(der: &[u8]) -> Result<Self, MldsaError> {
        let info = PrivateKeyInfoRef::from_der(der)?;
        let parameter_set = MldsaParameterSet::try_from(&info.algorithm)?;
        let key = Self {
            parameter_set,
            seed: Self::decode_seed(parameter_set, info.private_key.as_bytes())?,
        };
        if let Some(public_key) = info.public_key
            && public_key.as_bytes() != Some(key.public_key().as_bytes())
        {
            return Err(MldsaError::ParseError(
                "public key does not match the private key".into(),
            ));
        }
        Ok(key)
    }

    /// Decodes an ML-DSA private key from a PEM encoded PKCS#8{v1, v2}.
    fn from_pem_bytes(pem: &[u8]) -> Result<Self, MldsaError> {
        Self::from_der(&decode_pem(pem, "PRIVATE KEY")?)
    }
}

impl EncodeKey for MldsaSecretKey {
    /// Encodes the ML-DSA private key as a DER encoded PKCS#8v1 holding the seed.
    fn to_der(&self) -> Result<Vec<u8>, MldsaError> {
        let seed = Zeroizing::new(
            ContextSpecific {
                tag_number: SEED_TAG_NUMBER,
                tag_mode: TagMode::Implicit,
                value: OctetStringRef::new(&self.seed)?,
            }
            .to_der()?,
        );
        let info = PrivateKeyInfoRef::new(self.parameter_set.into(), OctetStringRef::new(&seed)?);
        Ok(info.to_der()?)
    }

    /// Encodes the ML-DSA private key as a PEM encoded PKCS#8v1.
    fn to_pem(&self) -> Result<String, MldsaError> {
        encode_pem(&Zeroizing::new(self.to_der()?), "PRIVATE KEY")
    }
}

impl MldsaPublicKey {
    /// Creates an ML-DSA public key from raw bytes.
    pub fn from_bytes(parameter_set: MldsaParameterSet, bytes: &[u8]) -> Result<Self, MldsaError> {
        if bytes.len() != parameter_set.public_key_len() {
            return Err(MldsaError::BadKeyLength(bytes.len()));
        }
        Ok(Self {
            parameter_set,
            key: bytes.to_vec(),
        })
    }

    /// Returns the parameter set of this key.
    pub fn parameter_set(&self) -> MldsaParameterSet {
        self.parameter_set
    }

    /// Returns the raw key bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.key.as_slice()
    }

    /// Verifies the signature and message with the public key under the given
    /// context string (pure ML-DSA).
    pub fn verify(&self, context: &[u8], signature: &[u8], msg: &[u8]) -> Result<(), MldsaError> {
        self.parameter_set
            .verify(&self.key, context, signature, msg)
    }
}

impl DecodeKey for MldsaPublicKey {
    /// Decodes an ML-DSA public key from a DER encoded SubjectPublicKeyInfo.
    fn from_der(der: &[u8]) -> Result<Self, MldsaError> {
        let spki = SubjectPublicKeyInfoRef::from_der(der)?;
        let parameter_set = MldsaParameterSet::try_from(&spki.algorithm)?;
        let key = spki.subject_public_key.as_bytes().ok_or_else(|| {
            MldsaError::ParseError("public key is not a whole number of bytes".into())
        })?;
        Self::from_bytes(parameter_set, key)
    }

    /// Decodes an ML-DSA public key from a PEM encoded SubjectPublicKeyInfo.
    fn from_pem_bytes(pem: &[u8]) -> Result<Self, MldsaError> {
        Self::from_der(&decode_pem(pem, "PUBLIC KEY")?)
    }
}

impl EncodeKey for MldsaPublicKey {
    /// Encodes the ML-DSA public key as a DER encoded SubjectPublicKeyInfo.
    fn to_der(&self) -> Result<Vec<u8>, MldsaError> {
        Ok(SubjectPublicKeyInfoRef {
            algorithm: self.parameter_set.into(),
            subject_public_key: BitStringRef::new(0, &self.key)?,
        }
        .to_der()?)
    }

    /// Encodes the ML-DSA public key as a PEM encoded SubjectPublicKeyInfo.
    fn to_pem(&self) -> Result<String, MldsaError> {
        encode_pem(&self.to_der()?, "PUBLIC KEY")
    }
}

impl From<&MldsaSecretKey> for MldsaPublicKey {
    /// Derives the public key of a private key.
    fn from(sk: &MldsaSecretKey) -> Self {
        sk.public_key()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::variants::MAX_CONTEXT_LEN;

    #[test]
    fn key_encoding() -> Result<(), MldsaError> {
        let parameter_set = MldsaParameterSet::Mldsa87;
        let sk = MldsaSecretKey::generate(parameter_set)?;
        let pk = sk.public_key();
        assert_eq!(pk.as_bytes().len(), parameter_set.public_key_len());

        // Private key encode/decode.
        let decoded = MldsaSecretKey::from_pem(&sk.to_pem()?)?;
        assert_eq!(decoded, sk);
        assert_eq!(decoded.parameter_set(), parameter_set);
        assert_eq!(MldsaSecretKey::from_der(&sk.to_der()?)?, sk);

        // Public key encode/decode.
        let decoded = MldsaPublicKey::from_pem(&pk.to_pem()?)?;
        assert_eq!(decoded, pk);
        assert_eq!(decoded.parameter_set(), parameter_set);
        assert_eq!(MldsaPublicKey::from_der(&pk.to_der()?)?, pk);
        Ok(())
    }

    #[test]
    fn key_type_mismatch() -> Result<(), MldsaError> {
        let sk = MldsaSecretKey::generate(MldsaParameterSet::Mldsa87)?;
        let pk = sk.public_key();
        // A private key cannot be loaded from a public key and vice versa.
        assert!(MldsaSecretKey::from_pem(&pk.to_pem()?).is_err());
        assert!(MldsaSecretKey::from_der(&pk.to_der()?).is_err());
        assert!(MldsaPublicKey::from_pem(&sk.to_pem()?).is_err());
        assert!(MldsaPublicKey::from_der(&sk.to_der()?).is_err());
        Ok(())
    }

    /// Encodes `sk` as a PKCS#8v2 (OneAsymmetricKey) containing `pk`.
    fn to_pkcs8_v2(sk: &MldsaSecretKey, pk: &MldsaPublicKey) -> Result<Vec<u8>, MldsaError> {
        let v1 = sk.to_der()?;
        let mut info = PrivateKeyInfoRef::from_der(&v1)?;
        info.public_key = Some(BitStringRef::new(0, pk.as_bytes())?);
        Ok(info.to_der()?)
    }

    #[test]
    fn pkcs8_v2() -> Result<(), MldsaError> {
        let sk = MldsaSecretKey::generate(MldsaParameterSet::Mldsa87)?;
        assert_eq!(
            MldsaSecretKey::from_der(&to_pkcs8_v2(&sk, &sk.public_key())?)?,
            sk
        );

        // The public key must match the private key.
        let other = MldsaSecretKey::generate(MldsaParameterSet::Mldsa87)?;
        assert!(matches!(
            MldsaSecretKey::from_der(&to_pkcs8_v2(&sk, &other.public_key())?),
            Err(MldsaError::ParseError(_))
        ));
        Ok(())
    }

    #[test]
    fn sign_verify() -> Result<(), MldsaError> {
        let parameter_set = MldsaParameterSet::Mldsa87;
        let sk = MldsaSecretKey::generate(parameter_set)?;
        let pk = sk.public_key();
        let sig = sk.sign(b"context", b"message")?;
        assert_eq!(sig.len(), parameter_set.signature_len());
        pk.verify(b"context", &sig, b"message")?;
        assert!(matches!(
            pk.verify(b"other", &sig, b"message"),
            Err(MldsaError::BadSignature)
        ));
        assert!(matches!(
            pk.verify(b"context", &sig, b"other"),
            Err(MldsaError::BadSignature)
        ));
        assert!(matches!(
            pk.verify(b"context", &sig[1..], b"message"),
            Err(MldsaError::BadSigLength(_))
        ));

        // The context string may be at most 255 bytes long.
        let context = [0x5au8; MAX_CONTEXT_LEN];
        let sig = sk.sign(&context, b"message")?;
        pk.verify(&context, &sig, b"message")?;
        assert!(matches!(
            sk.sign(&[0u8; MAX_CONTEXT_LEN + 1], b"message"),
            Err(MldsaError::BadContextLength(_))
        ));
        assert!(matches!(
            pk.verify(&[0u8; MAX_CONTEXT_LEN + 1], &sig, b"message"),
            Err(MldsaError::BadContextLength(_))
        ));
        Ok(())
    }

    /// Known answer test vector: generated with OpenSSL 3.5.
    const KAT_MESSAGE: &[u8] = b"The quick brown fox jumps over the lazy dog";
    const KAT_CONTEXT: &[u8] = b"OpenTitan";
    const KAT_PUBLIC: &str = include_str!("testdata/mldsa87.pub.pem");
    const KAT_SIGNATURE: &[u8] = include_bytes!("testdata/mldsa87.sig");

    #[test]
    fn known_answer() -> Result<(), MldsaError> {
        MldsaPublicKey::from_pem(KAT_PUBLIC)?.verify(KAT_CONTEXT, KAT_SIGNATURE, KAT_MESSAGE)
    }

    /// Private keys generated with OpenSSL 3.5 in its three output formats.
    const OPENSSL_SEED_PRIV: &str = include_str!("testdata/openssl_mldsa87.seed-priv.pem");
    const OPENSSL_SEED_ONLY: &str = include_str!("testdata/openssl_mldsa87.seed-only.pem");
    const OPENSSL_PRIV_ONLY: &str = include_str!("testdata/openssl_mldsa87.priv-only.pem");
    const OPENSSL_PUBLIC: &str = include_str!("testdata/openssl_mldsa87.pub.pem");

    #[test]
    fn openssl_interop() -> Result<(), MldsaError> {
        let pk = MldsaPublicKey::from_pem(OPENSSL_PUBLIC)?;
        let both = MldsaSecretKey::from_pem(OPENSSL_SEED_PRIV)?;
        let seed = MldsaSecretKey::from_pem(OPENSSL_SEED_ONLY)?;
        assert_eq!(both, seed);
        assert_eq!(seed.public_key(), pk);
        // Our encoding matches OpenSSL's seed-only encoding.
        assert_eq!(seed.to_pem()?, OPENSSL_SEED_ONLY.replace("\r\n", "\n"));
        let err = MldsaSecretKey::from_pem(OPENSSL_PRIV_ONLY).unwrap_err();
        assert!(err.to_string().contains("expanded-only"));
        Ok(())
    }
}
