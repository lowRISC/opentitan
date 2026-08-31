// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::mechanism::dsa::{HashSignAdditionalContext, HedgeType, SignAdditionalContext};
use cryptoki::mechanism::{Mechanism, MechanismType};
use rsa::pkcs8;
use rsa::pkcs8::spki;
use rsa::pkcs8::{
    DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, Error, LineEnding,
};
use slh_dsa::{SigningKey, VerifyingKey};
use sphincsplus::SpxDomain;
use std::path::Path;

use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::key::KeyEncoding;

fn _load_private_key(path: &Path) -> Result<SlhDsaPrivateKey> {
    let data = std::fs::read_to_string(path)?;
    if let Ok(sk) = SlhDsaPrivateKey::from_pkcs8_pem(&data) {
        return Ok(sk);
    }
    if let Ok(sk) = SlhDsaPrivateKey::from_pkcs8_der(data.as_bytes()) {
        return Ok(sk);
    }
    Err(anyhow!("Invalid Private Key PEM/DER"))
}

fn _load_public_key(path: &Path) -> Result<SlhDsaPublicKey> {
    let data = std::fs::read_to_string(path)?;
    if let Ok(sk) = SlhDsaPublicKey::from_public_key_pem(&data) {
        return Ok(sk);
    }
    if let Ok(sk) = SlhDsaPublicKey::from_public_key_der(data.as_bytes()) {
        return Ok(sk);
    }
    Err(anyhow!("Invalid Public Key PEM/DER"))
}

pub fn load_private_key<P: AsRef<Path>>(path: P) -> Result<SlhDsaPrivateKey> {
    _load_private_key(path.as_ref())
}

pub fn load_public_key<P: AsRef<Path>>(path: P) -> Result<SlhDsaPublicKey> {
    _load_public_key(path.as_ref())
}

fn _save_private_key(path: &Path, key: &SlhDsaPrivateKey, enc: KeyEncoding) -> Result<()> {
    match enc {
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => key.write_pkcs8_der_file(path)?,
        KeyEncoding::Pem | KeyEncoding::Pkcs8Pem | KeyEncoding::Pkcs8 => {
            key.write_pkcs8_pem_file(path, LineEnding::LF)?
        }
        _ => Err(HsmError::Unsupported("Unsupported output format".into()))?,
    };
    Ok(())
}

fn _save_public_key(path: &Path, key: &SlhDsaPublicKey, enc: KeyEncoding) -> Result<()> {
    match enc {
        KeyEncoding::Der => key.write_public_key_der_file(path)?,
        KeyEncoding::Pem => key.write_public_key_pem_file(path, LineEnding::LF)?,
        _ => Err(HsmError::Unsupported("Unsupported output format".into()))?,
    };
    Ok(())
}

pub fn save_private_key<P: AsRef<Path>>(
    path: P,
    key: &SlhDsaPrivateKey,
    enc: KeyEncoding,
) -> Result<()> {
    _save_private_key(path.as_ref(), key, enc)
}

pub fn save_public_key<P: AsRef<Path>>(
    path: P,
    key: &SlhDsaPublicKey,
    enc: KeyEncoding,
) -> Result<()> {
    _save_public_key(path.as_ref(), key, enc)
}

pub enum SlhDsaPrivateKey {
    Sha2_128s(SigningKey<slh_dsa::Sha2_128s>),
    Sha2_128f(SigningKey<slh_dsa::Sha2_128f>),
    Sha2_192s(SigningKey<slh_dsa::Sha2_192s>),
    Sha2_192f(SigningKey<slh_dsa::Sha2_192f>),
    Sha2_256s(SigningKey<slh_dsa::Sha2_256s>),
    Sha2_256f(SigningKey<slh_dsa::Sha2_256f>),
    Shake128s(SigningKey<slh_dsa::Shake128s>),
    Shake128f(SigningKey<slh_dsa::Shake128f>),
    Shake192s(SigningKey<slh_dsa::Shake192s>),
    Shake192f(SigningKey<slh_dsa::Shake192f>),
    Shake256s(SigningKey<slh_dsa::Shake256s>),
    Shake256f(SigningKey<slh_dsa::Shake256f>),
}

pub enum SlhDsaPublicKey {
    Sha2_128s(VerifyingKey<slh_dsa::Sha2_128s>),
    Sha2_128f(VerifyingKey<slh_dsa::Sha2_128f>),
    Sha2_192s(VerifyingKey<slh_dsa::Sha2_192s>),
    Sha2_192f(VerifyingKey<slh_dsa::Sha2_192f>),
    Sha2_256s(VerifyingKey<slh_dsa::Sha2_256s>),
    Sha2_256f(VerifyingKey<slh_dsa::Sha2_256f>),
    Shake128s(VerifyingKey<slh_dsa::Shake128s>),
    Shake128f(VerifyingKey<slh_dsa::Shake128f>),
    Shake192s(VerifyingKey<slh_dsa::Shake192s>),
    Shake192f(VerifyingKey<slh_dsa::Shake192f>),
    Shake256s(VerifyingKey<slh_dsa::Shake256s>),
    Shake256f(VerifyingKey<slh_dsa::Shake256f>),
}

impl EncodePrivateKey for SlhDsaPrivateKey {
    fn to_pkcs8_der(&self) -> pkcs8::Result<der::SecretDocument> {
        match self {
            Self::Sha2_128s(x) => x.to_pkcs8_der(),
            Self::Sha2_128f(x) => x.to_pkcs8_der(),
            Self::Sha2_192s(x) => x.to_pkcs8_der(),
            Self::Sha2_192f(x) => x.to_pkcs8_der(),
            Self::Sha2_256s(x) => x.to_pkcs8_der(),
            Self::Sha2_256f(x) => x.to_pkcs8_der(),
            Self::Shake128s(x) => x.to_pkcs8_der(),
            Self::Shake128f(x) => x.to_pkcs8_der(),
            Self::Shake192s(x) => x.to_pkcs8_der(),
            Self::Shake192f(x) => x.to_pkcs8_der(),
            Self::Shake256s(x) => x.to_pkcs8_der(),
            Self::Shake256f(x) => x.to_pkcs8_der(),
        }
    }
}

impl EncodePublicKey for SlhDsaPublicKey {
    fn to_public_key_der(&self) -> spki::Result<der::Document> {
        match self {
            Self::Sha2_128s(x) => x.to_public_key_der(),
            Self::Sha2_128f(x) => x.to_public_key_der(),
            Self::Sha2_192s(x) => x.to_public_key_der(),
            Self::Sha2_192f(x) => x.to_public_key_der(),
            Self::Sha2_256s(x) => x.to_public_key_der(),
            Self::Sha2_256f(x) => x.to_public_key_der(),
            Self::Shake128s(x) => x.to_public_key_der(),
            Self::Shake128f(x) => x.to_public_key_der(),
            Self::Shake192s(x) => x.to_public_key_der(),
            Self::Shake192f(x) => x.to_public_key_der(),
            Self::Shake256s(x) => x.to_public_key_der(),
            Self::Shake256f(x) => x.to_public_key_der(),
        }
    }
}

impl DecodePrivateKey for SlhDsaPrivateKey {
    fn from_pkcs8_der(bytes: &[u8]) -> pkcs8::Result<Self> {
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_128s>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_128s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_128f>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_128f(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_192s>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_192s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_192f>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_192f(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_256s>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_256s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Sha2_256f>::from_pkcs8_der(bytes) {
            return Ok(Self::Sha2_256f(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake128s>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake128s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake128f>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake128f(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake192s>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake192s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake192f>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake192f(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake256s>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake256s(sk));
        }
        if let Ok(sk) = SigningKey::<slh_dsa::Shake256f>::from_pkcs8_der(bytes) {
            return Ok(Self::Shake256f(sk));
        }
        Err(Error::KeyMalformed)
    }
}

impl DecodePublicKey for SlhDsaPublicKey {
    fn from_public_key_der(bytes: &[u8]) -> spki::Result<Self> {
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_128s>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_128s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_128f>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_128f(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_192s>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_192s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_192f>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_192f(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_256s>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_256s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Sha2_256f>::from_public_key_der(bytes) {
            return Ok(Self::Sha2_256f(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake128s>::from_public_key_der(bytes) {
            return Ok(Self::Shake128s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake128f>::from_public_key_der(bytes) {
            return Ok(Self::Shake128f(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake192s>::from_public_key_der(bytes) {
            return Ok(Self::Shake192s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake192f>::from_public_key_der(bytes) {
            return Ok(Self::Shake192f(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake256s>::from_public_key_der(bytes) {
            return Ok(Self::Shake256s(sk));
        }
        if let Ok(sk) = VerifyingKey::<slh_dsa::Shake256f>::from_public_key_der(bytes) {
            return Ok(Self::Shake256f(sk));
        }
        Err(Error::KeyMalformed.into())
    }
}

impl SlhDsaPrivateKey {
    pub fn to_vec(&self) -> Vec<u8> {
        match self {
            Self::Sha2_128s(x) => x.to_vec(),
            Self::Sha2_128f(x) => x.to_vec(),
            Self::Sha2_192s(x) => x.to_vec(),
            Self::Sha2_192f(x) => x.to_vec(),
            Self::Sha2_256s(x) => x.to_vec(),
            Self::Sha2_256f(x) => x.to_vec(),
            Self::Shake128s(x) => x.to_vec(),
            Self::Shake128f(x) => x.to_vec(),
            Self::Shake192s(x) => x.to_vec(),
            Self::Shake192f(x) => x.to_vec(),
            Self::Shake256s(x) => x.to_vec(),
            Self::Shake256f(x) => x.to_vec(),
        }
    }
}

impl SlhDsaPublicKey {
    pub fn to_vec(&self) -> Vec<u8> {
        match self {
            Self::Sha2_128s(x) => x.to_vec(),
            Self::Sha2_128f(x) => x.to_vec(),
            Self::Sha2_192s(x) => x.to_vec(),
            Self::Sha2_192f(x) => x.to_vec(),
            Self::Sha2_256s(x) => x.to_vec(),
            Self::Sha2_256f(x) => x.to_vec(),
            Self::Shake128s(x) => x.to_vec(),
            Self::Shake128f(x) => x.to_vec(),
            Self::Shake192s(x) => x.to_vec(),
            Self::Shake192f(x) => x.to_vec(),
            Self::Shake256s(x) => x.to_vec(),
            Self::Shake256f(x) => x.to_vec(),
        }
    }
}

impl TryFrom<&AttributeMap> for SlhDsaPrivateKey {
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
        if class != ObjectClass::PrivateKey || key_type != KeyType::SlhDsa {
            return Err(HsmError::KeyError(
                " Key is not an SLH-DSA Private Key".into(),
            ));
        }

        let parameter_set = map
            .get(&AttributeType::ParameterSet)
            .ok_or_else(|| HsmError::KeyError("Missing key parameter set".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Missing key value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value = value.as_slice();

        let key = match parameter_set {
            cryptoki_sys::CKP_SLH_DSA_SHA2_128S => {
                let key = SigningKey::<slh_dsa::Sha2_128s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_128s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_128F => {
                let key = SigningKey::<slh_dsa::Sha2_128f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_128f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_192S => {
                let key = SigningKey::<slh_dsa::Sha2_192s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_192s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_192F => {
                let key = SigningKey::<slh_dsa::Sha2_192f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_192f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_256S => {
                let key = SigningKey::<slh_dsa::Sha2_256s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_256s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_256F => {
                let key = SigningKey::<slh_dsa::Sha2_256f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Sha2_256f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_128S => {
                let key = SigningKey::<slh_dsa::Shake128s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake128s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_128F => {
                let key = SigningKey::<slh_dsa::Shake128f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake128f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_192S => {
                let key = SigningKey::<slh_dsa::Shake192s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake192s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_192F => {
                let key = SigningKey::<slh_dsa::Shake192f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake192f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_256S => {
                let key = SigningKey::<slh_dsa::Shake256s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake256s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_256F => {
                let key = SigningKey::<slh_dsa::Shake256f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPrivateKey::Shake256f(key)
            }
            _ => Err(HsmError::KeyError("Invalid parameter set for key".into()))?,
        };

        Ok(key)
    }
}

impl TryFrom<&AttributeMap> for SlhDsaPublicKey {
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
        if class != ObjectClass::PublicKey || key_type != KeyType::SlhDsa {
            return Err(HsmError::KeyError(
                " Key is not an SLH-DSA Public Key".into(),
            ));
        }

        let parameter_set = map
            .get(&AttributeType::ParameterSet)
            .ok_or_else(|| HsmError::KeyError("Missing key parameter set".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Missing key value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let value = value.as_slice();

        let key = match parameter_set {
            cryptoki_sys::CKP_SLH_DSA_SHA2_128S => {
                let key = VerifyingKey::<slh_dsa::Sha2_128s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_128s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_128F => {
                let key = VerifyingKey::<slh_dsa::Sha2_128f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_128f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_192S => {
                let key = VerifyingKey::<slh_dsa::Sha2_192s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_192s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_192F => {
                let key = VerifyingKey::<slh_dsa::Sha2_192f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_192f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_256S => {
                let key = VerifyingKey::<slh_dsa::Sha2_256s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_256s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHA2_256F => {
                let key = VerifyingKey::<slh_dsa::Sha2_256f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Sha2_256f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_128S => {
                let key = VerifyingKey::<slh_dsa::Shake128s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake128s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_128F => {
                let key = VerifyingKey::<slh_dsa::Shake128f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake128f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_192S => {
                let key = VerifyingKey::<slh_dsa::Shake192s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake192s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_192F => {
                let key = VerifyingKey::<slh_dsa::Shake192f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake192f(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_256S => {
                let key = VerifyingKey::<slh_dsa::Shake256s>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake256s(key)
            }
            cryptoki_sys::CKP_SLH_DSA_SHAKE_256F => {
                let key = VerifyingKey::<slh_dsa::Shake256f>::try_from(value)
                    .map_err(|_| HsmError::KeyError("Invalid key".into()))?;
                SlhDsaPublicKey::Shake256f(key)
            }
            _ => Err(HsmError::KeyError("Invalid parameter set for key".into()))?,
        };

        Ok(key)
    }
}

impl From<&SlhDsaPrivateKey> for SlhDsaPublicKey {
    fn from(sk: &SlhDsaPrivateKey) -> Self {
        match sk {
            SlhDsaPrivateKey::Sha2_128s(x) => SlhDsaPublicKey::Sha2_128s(x.as_ref().clone()),
            SlhDsaPrivateKey::Sha2_128f(x) => SlhDsaPublicKey::Sha2_128f(x.as_ref().clone()),
            SlhDsaPrivateKey::Sha2_192s(x) => SlhDsaPublicKey::Sha2_192s(x.as_ref().clone()),
            SlhDsaPrivateKey::Sha2_192f(x) => SlhDsaPublicKey::Sha2_192f(x.as_ref().clone()),
            SlhDsaPrivateKey::Sha2_256s(x) => SlhDsaPublicKey::Sha2_256s(x.as_ref().clone()),
            SlhDsaPrivateKey::Sha2_256f(x) => SlhDsaPublicKey::Sha2_256f(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake128s(x) => SlhDsaPublicKey::Shake128s(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake128f(x) => SlhDsaPublicKey::Shake128f(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake192s(x) => SlhDsaPublicKey::Shake192s(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake192f(x) => SlhDsaPublicKey::Shake192f(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake256s(x) => SlhDsaPublicKey::Shake256s(x.as_ref().clone()),
            SlhDsaPrivateKey::Shake256f(x) => SlhDsaPublicKey::Shake256f(x.as_ref().clone()),
        }
    }
}

impl From<SlhDsaPrivateKey> for AttributeMap {
    fn from(sk: SlhDsaPrivateKey) -> Self {
        let (parameter_set, value) = match sk {
            SlhDsaPrivateKey::Sha2_128s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_128S, x.to_vec()),
            SlhDsaPrivateKey::Sha2_128f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_128F, x.to_vec()),
            SlhDsaPrivateKey::Sha2_192s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_192S, x.to_vec()),
            SlhDsaPrivateKey::Sha2_192f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_192F, x.to_vec()),
            SlhDsaPrivateKey::Sha2_256s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_256S, x.to_vec()),
            SlhDsaPrivateKey::Sha2_256f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_256F, x.to_vec()),
            SlhDsaPrivateKey::Shake128s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_128S, x.to_vec()),
            SlhDsaPrivateKey::Shake128f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_128F, x.to_vec()),
            SlhDsaPrivateKey::Shake192s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_192S, x.to_vec()),
            SlhDsaPrivateKey::Shake192f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_192F, x.to_vec()),
            SlhDsaPrivateKey::Shake256s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_256S, x.to_vec()),
            SlhDsaPrivateKey::Shake256f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_256F, x.to_vec()),
        };
        let mut map = AttributeMap::default();
        map.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PrivateKey),
        );
        map.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::SlhDsa));
        map.insert(AttributeType::ParameterSet, parameter_set.into());
        map.insert(AttributeType::Value, value.as_slice().into());
        map
    }
}

impl From<SlhDsaPublicKey> for AttributeMap {
    fn from(sk: SlhDsaPublicKey) -> Self {
        let (parameter_set, value) = match &sk {
            SlhDsaPublicKey::Sha2_128s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_128S, x.to_vec()),
            SlhDsaPublicKey::Sha2_128f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_128F, x.to_vec()),
            SlhDsaPublicKey::Sha2_192s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_192S, x.to_vec()),
            SlhDsaPublicKey::Sha2_192f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_192F, x.to_vec()),
            SlhDsaPublicKey::Sha2_256s(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_256S, x.to_vec()),
            SlhDsaPublicKey::Sha2_256f(x) => (cryptoki_sys::CKP_SLH_DSA_SHA2_256F, x.to_vec()),
            SlhDsaPublicKey::Shake128s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_128S, x.to_vec()),
            SlhDsaPublicKey::Shake128f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_128F, x.to_vec()),
            SlhDsaPublicKey::Shake192s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_192S, x.to_vec()),
            SlhDsaPublicKey::Shake192f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_192F, x.to_vec()),
            SlhDsaPublicKey::Shake256s(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_256S, x.to_vec()),
            SlhDsaPublicKey::Shake256f(x) => (cryptoki_sys::CKP_SLH_DSA_SHAKE_256F, x.to_vec()),
        };
        let mut map = AttributeMap::default();
        map.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PublicKey),
        );
        map.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::SlhDsa));
        map.insert(AttributeType::ParameterSet, parameter_set.into());
        map.insert(AttributeType::Value, value.as_slice().into());
        map
    }
}

pub trait SlhDsaMechanism {
    fn slh_dsa_mechanism(&self) -> Mechanism<'_>;
}

impl SlhDsaMechanism for SpxDomain {
    fn slh_dsa_mechanism(&self) -> Mechanism<'_> {
        match self {
            SpxDomain::None | SpxDomain::Pure => {
                Mechanism::SlhDsa(SignAdditionalContext::new(HedgeType::Preferred, None))
            }
            // In PKCS#11, there are separate CKM_HASH_SLH_DSA and CKM_HASH_SLH_DSA_*
            // mechanisms, where the latter expect the full message and perform the hashing
            // on token. Since our data is pre-hashed for this domain, use the former
            // and specify SHA-256 as the hash already used.
            SpxDomain::PreHashedSha256 => Mechanism::HashSlhDsa(HashSignAdditionalContext::new(
                HedgeType::Preferred,
                None,
                MechanismType::SHA256,
            )),
        }
    }
}
