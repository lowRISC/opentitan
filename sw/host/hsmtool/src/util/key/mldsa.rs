// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Context, Result};
use const_oid::ObjectIdentifier;
use der::{Encode, EncodePem};
use ml_dsa::{
    EncodedSigningKey, EncodedVerifyingKey, MlDsa44, MlDsa65, MlDsa87, SigningKey,
    VerifyingKey,
};
use pem_rfc7468;
use pkcs8::{DecodePrivateKey, PrivateKeyInfo};
use spki::{AssociatedAlgorithmIdentifier, DecodePublicKey, EncodePublicKey};
use std::convert::{AsRef, TryFrom};
use std::path::Path;

use super::KeyEncoding;
use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};

pub enum MldsaSigningKey {
    V44(Box<SigningKey<MlDsa44>>),
    V65(Box<SigningKey<MlDsa65>>),
    V87(Box<SigningKey<MlDsa87>>),
}

impl MldsaSigningKey {
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Self::V44(k) => k.encode().to_vec(),
            Self::V65(k) => k.encode().to_vec(),
            Self::V87(k) => k.encode().to_vec(),
        }
    }

    pub fn parameter_set(&self) -> u64 {
        match self {
            Self::V44(_) => 1,
            Self::V65(_) => 2,
            Self::V87(_) => 3,
        }
    }

    pub fn oid(&self) -> ObjectIdentifier {
        match self {
            Self::V44(_) => MlDsa44::ALGORITHM_IDENTIFIER.oid,
            Self::V65(_) => MlDsa65::ALGORITHM_IDENTIFIER.oid,
            Self::V87(_) => MlDsa87::ALGORITHM_IDENTIFIER.oid,
        }
    }
}

pub enum MldsaVerifyingKey {
    V44(Box<VerifyingKey<MlDsa44>>),
    V65(Box<VerifyingKey<MlDsa65>>),
    V87(Box<VerifyingKey<MlDsa87>>),
}

impl MldsaVerifyingKey {
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Self::V44(k) => k.encode().to_vec(),
            Self::V65(k) => k.encode().to_vec(),
            Self::V87(k) => k.encode().to_vec(),
        }
    }

    pub fn parameter_set(&self) -> u64 {
        match self {
            Self::V44(_) => 1,
            Self::V65(_) => 2,
            Self::V87(_) => 3,
        }
    }

    pub fn oid(&self) -> ObjectIdentifier {
        match self {
            Self::V44(_) => MlDsa44::ALGORITHM_IDENTIFIER.oid,
            Self::V65(_) => MlDsa65::ALGORITHM_IDENTIFIER.oid,
            Self::V87(_) => MlDsa87::ALGORITHM_IDENTIFIER.oid,
        }
    }
}

fn _load_private_key(path: &Path) -> Result<MldsaSigningKey> {
    let data = std::fs::read(path)?;
    let der_bytes = if let Ok((_label, bytes)) = pem_rfc7468::decode_vec(&data) {
        bytes
    } else {
        data
    };

    if let Ok(key) = SigningKey::<MlDsa44>::from_pkcs8_der(&der_bytes) {
        Ok(MldsaSigningKey::V44(Box::new(key)))
    } else if let Ok(key) = SigningKey::<MlDsa65>::from_pkcs8_der(&der_bytes) {
        Ok(MldsaSigningKey::V65(Box::new(key)))
    } else if let Ok(key) = SigningKey::<MlDsa87>::from_pkcs8_der(&der_bytes) {
        Ok(MldsaSigningKey::V87(Box::new(key)))
    } else {
        Err(anyhow!("Could not decode MLDSA private key from PKCS#8 DER"))
    }
}

pub fn load_private_key<P: AsRef<Path>>(path: P) -> Result<MldsaSigningKey> {
    _load_private_key(path.as_ref())
}

impl TryFrom<&MldsaSigningKey> for AttributeMap {
    type Error = HsmError;
    fn try_from(k: &MldsaSigningKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PrivateKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::MlDsa));
        attr.insert(AttributeType::ParameterSet, AttrData::from(k.parameter_set()));
        attr.insert(AttributeType::Value, AttrData::from(k.encode().as_slice()));
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for MldsaSigningKey {
    type Error = HsmError;
    fn try_from(a: &AttributeMap) -> std::result::Result<Self, Self::Error> {
        let class: ObjectClass = a
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("missing class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = a
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("missing key_type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PrivateKey || key_type != KeyType::MlDsa {
            return Err(HsmError::KeyError("bad key type".into()));
        }

        let value: Vec<u8> = a
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("missing value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        // Try to determine the parameter set from AttributeType::ParameterSet if available
        let parameter_set = a
            .get(&AttributeType::ParameterSet)
            .and_then(|d| u64::try_from(d).ok());

        match parameter_set {
            Some(1) => {
                let arr = EncodedSigningKey::<MlDsa44>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-44 key length".into()))?;
                Ok(MldsaSigningKey::V44(Box::new(SigningKey::<MlDsa44>::decode(
                    &arr,
                ))))
            }
            Some(2) => {
                let arr = EncodedSigningKey::<MlDsa65>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-65 key length".into()))?;
                Ok(MldsaSigningKey::V65(Box::new(SigningKey::<MlDsa65>::decode(
                    &arr,
                ))))
            }
            Some(3) => {
                let arr = EncodedSigningKey::<MlDsa87>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-87 key length".into()))?;
                Ok(MldsaSigningKey::V87(Box::new(SigningKey::<MlDsa87>::decode(
                    &arr,
                ))))
            }
            _ => {
                // If parameter set is missing or unknown, try to guess from length
                if let Ok(arr) = EncodedSigningKey::<MlDsa44>::try_from(value.as_slice()) {
                    Ok(MldsaSigningKey::V44(Box::new(SigningKey::<MlDsa44>::decode(
                        &arr,
                    ))))
                } else if let Ok(arr) = EncodedSigningKey::<MlDsa65>::try_from(value.as_slice()) {
                    Ok(MldsaSigningKey::V65(Box::new(SigningKey::<MlDsa65>::decode(
                        &arr,
                    ))))
                } else if let Ok(arr) = EncodedSigningKey::<MlDsa87>::try_from(value.as_slice()) {
                    Ok(MldsaSigningKey::V87(Box::new(SigningKey::<MlDsa87>::decode(
                        &arr,
                    ))))
                } else {
                    Err(HsmError::KeyError("Could not decode MLDSA private key".into()))
                }
            }
        }
    }
}

fn _load_public_key(path: &Path) -> Result<MldsaVerifyingKey> {
    let data = std::fs::read(path)?;
    let der_bytes = if let Ok((_label, bytes)) = pem_rfc7468::decode_vec(&data) {
        bytes
    } else {
        data
    };

    if let Ok(key) = VerifyingKey::<MlDsa44>::from_public_key_der(&der_bytes) {
        Ok(MldsaVerifyingKey::V44(Box::new(key)))
    } else if let Ok(key) = VerifyingKey::<MlDsa65>::from_public_key_der(&der_bytes) {
        Ok(MldsaVerifyingKey::V65(Box::new(key)))
    } else if let Ok(key) = VerifyingKey::<MlDsa87>::from_public_key_der(&der_bytes) {
        Ok(MldsaVerifyingKey::V87(Box::new(key)))
    } else {
        Err(anyhow!("Could not decode MLDSA public key from SPKI DER"))
    }
}

pub fn load_public_key<P: AsRef<Path>>(path: P) -> Result<MldsaVerifyingKey> {
    _load_public_key(path.as_ref())
}

impl TryFrom<&MldsaVerifyingKey> for AttributeMap {
    type Error = HsmError;
    fn try_from(k: &MldsaVerifyingKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PublicKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::MlDsa));
        attr.insert(AttributeType::ParameterSet, AttrData::from(k.parameter_set()));
        attr.insert(AttributeType::Value, AttrData::from(k.encode().as_slice()));
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for MldsaVerifyingKey {
    type Error = HsmError;
    fn try_from(a: &AttributeMap) -> std::result::Result<Self, Self::Error> {
        let class: ObjectClass = a
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("missing class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = a
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("missing key_type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PublicKey || key_type != KeyType::MlDsa {
            return Err(HsmError::KeyError("bad key type".into()));
        }

        let value: Vec<u8> = a
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("missing value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        let parameter_set = a
            .get(&AttributeType::ParameterSet)
            .and_then(|d| u64::try_from(d).ok());

        match parameter_set {
            Some(1) => {
                let arr = EncodedVerifyingKey::<MlDsa44>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-44 key length".into()))?;
                Ok(MldsaVerifyingKey::V44(Box::new(
                    VerifyingKey::<MlDsa44>::decode(&arr),
                )))
            }
            Some(2) => {
                let arr = EncodedVerifyingKey::<MlDsa65>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-65 key length".into()))?;
                Ok(MldsaVerifyingKey::V65(Box::new(
                    VerifyingKey::<MlDsa65>::decode(&arr),
                )))
            }
            Some(3) => {
                let arr = EncodedVerifyingKey::<MlDsa87>::try_from(value.as_slice())
                    .map_err(|_| HsmError::KeyError("invalid MLDSA-87 key length".into()))?;
                Ok(MldsaVerifyingKey::V87(Box::new(
                    VerifyingKey::<MlDsa87>::decode(&arr),
                )))
            }
            _ => {
                if let Ok(arr) = EncodedVerifyingKey::<MlDsa44>::try_from(value.as_slice()) {
                    Ok(MldsaVerifyingKey::V44(Box::new(
                        VerifyingKey::<MlDsa44>::decode(&arr),
                    )))
                } else if let Ok(arr) = EncodedVerifyingKey::<MlDsa65>::try_from(value.as_slice()) {
                    Ok(MldsaVerifyingKey::V65(Box::new(
                        VerifyingKey::<MlDsa65>::decode(&arr),
                    )))
                } else if let Ok(arr) = EncodedVerifyingKey::<MlDsa87>::try_from(value.as_slice()) {
                    Ok(MldsaVerifyingKey::V87(Box::new(
                        VerifyingKey::<MlDsa87>::decode(&arr),
                    )))
                } else {
                    Err(HsmError::KeyError("Could not decode MLDSA public key".into()))
                }
            }
        }
    }
}

pub fn save_private_key<P: AsRef<Path>>(
    path: P,
    key: &MldsaSigningKey,
    enc: KeyEncoding,
) -> Result<()> {
    let encoded = key.encode();
    let pk_info = match key {
        MldsaSigningKey::V44(_) => PrivateKeyInfo::new(MlDsa44::ALGORITHM_IDENTIFIER, &encoded),
        MldsaSigningKey::V65(_) => PrivateKeyInfo::new(MlDsa65::ALGORITHM_IDENTIFIER, &encoded),
        MldsaSigningKey::V87(_) => PrivateKeyInfo::new(MlDsa87::ALGORITHM_IDENTIFIER, &encoded),
    };

    let data = match enc {
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => pk_info.to_der()?,
        KeyEncoding::Pem | KeyEncoding::Pkcs8Pem => {
            pk_info.to_pem(pkcs8::LineEnding::LF)?.as_bytes().to_vec()
        }
        _ => return Err(anyhow!("Unsupported format for MLDSA export: {:?}", enc)),
    };
    std::fs::write(path, data).context("Saving private key")
}

pub fn save_public_key<P: AsRef<Path>>(
    path: P,
    key: &MldsaVerifyingKey,
    enc: KeyEncoding,
) -> Result<()> {
    let data = match key {
        MldsaVerifyingKey::V44(k) => match enc {
            KeyEncoding::Der | KeyEncoding::Pkcs8Der => k.to_public_key_der()?.as_bytes().to_vec(),
            KeyEncoding::Pem | KeyEncoding::Pkcs8Pem => {
                k.to_public_key_pem(pkcs8::LineEnding::LF)?.as_bytes().to_vec()
            }
            _ => return Err(anyhow!("Unsupported format for MLDSA export")),
        },
        MldsaVerifyingKey::V65(k) => match enc {
            KeyEncoding::Der | KeyEncoding::Pkcs8Der => k.to_public_key_der()?.as_bytes().to_vec(),
            KeyEncoding::Pem | KeyEncoding::Pkcs8Pem => {
                k.to_public_key_pem(pkcs8::LineEnding::LF)?.as_bytes().to_vec()
            }
            _ => return Err(anyhow!("Unsupported format for MLDSA export")),
        },
        MldsaVerifyingKey::V87(k) => match enc {
            KeyEncoding::Der | KeyEncoding::Pkcs8Der => k.to_public_key_der()?.as_bytes().to_vec(),
            KeyEncoding::Pem | KeyEncoding::Pkcs8Pem => {
                k.to_public_key_pem(pkcs8::LineEnding::LF)?.as_bytes().to_vec()
            }
            _ => return Err(anyhow!("Unsupported format for MLDSA export")),
        },
    };
    std::fs::write(path, data).context("Saving public key")
}

#[cfg(test)]
mod tests {
    use super::*;
    use ml_dsa::{KeyGen, MlDsa44, MlDsa65, MlDsa87};
    use rand::thread_rng;

    #[test]
    fn test_mldsa44_convert() -> Result<()> {
        let mut rng = thread_rng();
        let kp = MlDsa44::key_gen(&mut rng);
        let key = MldsaSigningKey::V44(Box::new(kp.signing_key().clone()));

        let hsm = AttributeMap::try_from(&key)?;
        let key2 = MldsaSigningKey::try_from(&hsm)?;

        assert_eq!(key.encode(), key2.encode());
        assert_eq!(key.parameter_set(), 1);

        let vk = MldsaVerifyingKey::V44(Box::new(kp.verifying_key().clone()));
        let hsm_pub = AttributeMap::try_from(&vk)?;
        let vk2 = MldsaVerifyingKey::try_from(&hsm_pub)?;

        assert_eq!(vk.encode(), vk2.encode());
        assert_eq!(vk.parameter_set(), 1);
        Ok(())
    }

    #[test]
    fn test_mldsa65_convert() -> Result<()> {
        let mut rng = thread_rng();
        let kp = MlDsa65::key_gen(&mut rng);
        let key = MldsaSigningKey::V65(Box::new(kp.signing_key().clone()));

        let hsm = AttributeMap::try_from(&key)?;
        let key2 = MldsaSigningKey::try_from(&hsm)?;

        assert_eq!(key.encode(), key2.encode());
        assert_eq!(key.parameter_set(), 2);

        let vk = MldsaVerifyingKey::V65(Box::new(kp.verifying_key().clone()));
        let hsm_pub = AttributeMap::try_from(&vk)?;
        let vk2 = MldsaVerifyingKey::try_from(&hsm_pub)?;

        assert_eq!(vk.encode(), vk2.encode());
        assert_eq!(vk.parameter_set(), 2);
        Ok(())
    }

    #[test]
    fn test_mldsa87_convert() -> Result<()> {
        let mut rng = thread_rng();
        let kp = MlDsa87::key_gen(&mut rng);
        let key = MldsaSigningKey::V87(Box::new(kp.signing_key().clone()));

        let hsm = AttributeMap::try_from(&key)?;
        let key2 = MldsaSigningKey::try_from(&hsm)?;

        assert_eq!(key.encode(), key2.encode());
        assert_eq!(key.parameter_set(), 3);

        let vk = MldsaVerifyingKey::V87(Box::new(kp.verifying_key().clone()));
        let hsm_pub = AttributeMap::try_from(&vk)?;
        let vk2 = MldsaVerifyingKey::try_from(&hsm_pub)?;

        assert_eq!(vk.encode(), vk2.encode());
        assert_eq!(vk.parameter_set(), 3);
        Ok(())
    }
}
