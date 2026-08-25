// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::mechanism::Mechanism;
use cryptoki::mechanism::dsa::{HedgeType, SignAdditionalContext};
use der::Encode;
use der::asn1::BitStringRef;
use rsa::pkcs8::spki::{AlgorithmIdentifierRef, ObjectIdentifier, SubjectPublicKeyInfoRef};
use rsa::pkcs8::{
    self, EncodePrivateKey, EncodePublicKey, Error, LineEnding, PrivateKeyInfo, spki,
};
use std::path::Path;

use crate::error::HsmError;
use crate::util::attribute::{AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::key::KeyEncoding;

pub const ID_ML_DSA_44: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.3.17");
pub const ID_ML_DSA_65: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.3.18");
pub const ID_ML_DSA_87: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.16.840.1.101.3.4.3.19");

pub const ML_DSA_44_PUB_LEN: usize = 1312;
pub const ML_DSA_65_PUB_LEN: usize = 1952;
pub const ML_DSA_87_PUB_LEN: usize = 2592;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MldsaPrivateKey {
    MlDsa44(Vec<u8>),
    MlDsa65(Vec<u8>),
    MlDsa87(Vec<u8>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MldsaPublicKey {
    MlDsa44(Vec<u8>),
    MlDsa65(Vec<u8>),
    MlDsa87(Vec<u8>),
}

pub fn save_private_key(path: &Path, key: &MldsaPrivateKey, enc: KeyEncoding) -> Result<()> {
    match enc {
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => key.write_pkcs8_der_file(path)?,
        KeyEncoding::Pem | KeyEncoding::Pkcs8Pem | KeyEncoding::Pkcs8 => {
            key.write_pkcs8_pem_file(path, LineEnding::LF)?
        }
        _ => Err(HsmError::Unsupported("Unsupported output format".into()))?,
    };
    Ok(())
}

pub fn save_public_key(path: &Path, key: &MldsaPublicKey, enc: KeyEncoding) -> Result<()> {
    match enc {
        KeyEncoding::Der => key.write_public_key_der_file(path)?,
        KeyEncoding::Pem => key.write_public_key_pem_file(path, LineEnding::LF)?,
        _ => Err(HsmError::Unsupported("Unsupported output format".into()))?,
    };
    Ok(())
}

impl EncodePrivateKey for MldsaPrivateKey {
    fn to_pkcs8_der(&self) -> pkcs8::Result<der::SecretDocument> {
        let (oid, raw) = match self {
            Self::MlDsa44(x) => (ID_ML_DSA_44, x.as_slice()),
            Self::MlDsa65(x) => (ID_ML_DSA_65, x.as_slice()),
            Self::MlDsa87(x) => (ID_ML_DSA_87, x.as_slice()),
        };
        let pki = PrivateKeyInfo {
            algorithm: AlgorithmIdentifierRef {
                oid,
                parameters: None,
            },
            private_key: raw,
            public_key: None,
        };
        let mut buf = Vec::new();
        pki.encode_to_vec(&mut buf)
            .map_err(|_| Error::KeyMalformed)?;
        der::SecretDocument::try_from(buf.as_slice()).map_err(|_| Error::KeyMalformed)
    }
}

impl EncodePublicKey for MldsaPublicKey {
    fn to_public_key_der(&self) -> spki::Result<der::Document> {
        let (oid, raw) = match self {
            Self::MlDsa44(x) => (ID_ML_DSA_44, x.as_slice()),
            Self::MlDsa65(x) => (ID_ML_DSA_65, x.as_slice()),
            Self::MlDsa87(x) => (ID_ML_DSA_87, x.as_slice()),
        };
        let bit_string = BitStringRef::from_bytes(raw).map_err(|_| spki::Error::KeyMalformed)?;
        let spki_ref = SubjectPublicKeyInfoRef {
            algorithm: AlgorithmIdentifierRef {
                oid,
                parameters: None,
            },
            subject_public_key: bit_string,
        };
        let mut buf = Vec::new();
        spki_ref
            .encode_to_vec(&mut buf)
            .map_err(|_| spki::Error::KeyMalformed)?;
        der::Document::try_from(buf.as_slice()).map_err(|_| spki::Error::KeyMalformed)
    }
}

impl TryFrom<&AttributeMap> for MldsaPrivateKey {
    type Error = HsmError;

    fn try_from(map: &AttributeMap) -> Result<Self, Self::Error> {
        let class: ObjectClass = map
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("Missing key class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = map
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("Missing key type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PrivateKey || key_type != KeyType::MlDsa {
            return Err(HsmError::KeyError(
                "Key is not an ML-DSA Private Key".into(),
            ));
        }

        let parameter_set: u64 = map
            .get(&AttributeType::ParameterSet)
            .ok_or_else(|| HsmError::KeyError("Missing key parameter set".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Missing key value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        match parameter_set {
            cryptoki_sys::CKP_ML_DSA_44 => Ok(Self::MlDsa44(value)),
            cryptoki_sys::CKP_ML_DSA_65 => Ok(Self::MlDsa65(value)),
            cryptoki_sys::CKP_ML_DSA_87 => Ok(Self::MlDsa87(value)),
            _ => Err(HsmError::KeyError(
                "Invalid parameter set for ML-DSA key".into(),
            )),
        }
    }
}

impl TryFrom<&AttributeMap> for MldsaPublicKey {
    type Error = HsmError;

    fn try_from(map: &AttributeMap) -> Result<Self, Self::Error> {
        let class: ObjectClass = map
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("Missing key class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = map
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("Missing key type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PublicKey || key_type != KeyType::MlDsa {
            return Err(HsmError::KeyError("Key is not an ML-DSA Public Key".into()));
        }

        let parameter_set: u64 = map
            .get(&AttributeType::ParameterSet)
            .ok_or_else(|| HsmError::KeyError("Missing key parameter set".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Missing key value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        match parameter_set {
            cryptoki_sys::CKP_ML_DSA_44 => {
                if value.len() != ML_DSA_44_PUB_LEN {
                    return Err(HsmError::KeyError(
                        "Invalid public key length for ML-DSA-44".into(),
                    ));
                }
                Ok(Self::MlDsa44(value))
            }
            cryptoki_sys::CKP_ML_DSA_65 => {
                if value.len() != ML_DSA_65_PUB_LEN {
                    return Err(HsmError::KeyError(
                        "Invalid public key length for ML-DSA-65".into(),
                    ));
                }
                Ok(Self::MlDsa65(value))
            }
            cryptoki_sys::CKP_ML_DSA_87 => {
                if value.len() != ML_DSA_87_PUB_LEN {
                    return Err(HsmError::KeyError(
                        "Invalid public key length for ML-DSA-87".into(),
                    ));
                }
                Ok(Self::MlDsa87(value))
            }
            _ => Err(HsmError::KeyError(
                "Invalid parameter set for ML-DSA key".into(),
            )),
        }
    }
}

pub fn default_mldsa_mechanism() -> Mechanism<'static> {
    Mechanism::MlDsa(SignAdditionalContext::new(HedgeType::Preferred, None))
}
