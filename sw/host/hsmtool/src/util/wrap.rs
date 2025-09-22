// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module provides functionality for wrapping and unwrapping cryptographic
// keys using different mechanisms. It supports AES key wrap, AES key wrap with
// padding, and RSA PKCS OAEP.

use anyhow::{Ok, Result};
use clap::ValueEnum;
use cryptoki::mechanism::rsa::{PkcsMgfType, PkcsOaepParams, PkcsOaepSource};
use cryptoki::mechanism::vendor_defined::{CKM_VENDOR_DEFINED, VendorDefinedMechanism};
use cryptoki::mechanism::{Mechanism, MechanismType};
use cryptoki::object::{Attribute, ObjectHandle};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use strum::{Display, EnumString};

use crate::error::HsmError;
use crate::util::attribute::{AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;

/// The wrapping mechanism to use.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Display, EnumString, ValueEnum,
)]
#[strum(ascii_case_insensitive)]
pub enum Wrap {
    AesKeyWrap,
    AesKeyWrapPad,
    RsaPkcs,
    RsaPkcsOaep,
    VendorThalesAesKw,
    VendorThalesAesKwp,
}

/// The wrapping mechanism to use for private keys.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Display, EnumString, ValueEnum,
)]
#[strum(ascii_case_insensitive)]
pub enum WrapPrivateKey {
    AesKeyWrap,
    AesKeyWrapPad,
    VendorThalesAesKw,
    VendorThalesAesKwp,
}

impl From<WrapPrivateKey> for Wrap {
    fn from(wrap: WrapPrivateKey) -> Self {
        match wrap {
            WrapPrivateKey::AesKeyWrap => Wrap::AesKeyWrap,
            WrapPrivateKey::AesKeyWrapPad => Wrap::AesKeyWrapPad,
            WrapPrivateKey::VendorThalesAesKw => Wrap::VendorThalesAesKw,
            WrapPrivateKey::VendorThalesAesKwp => Wrap::VendorThalesAesKwp,
        }
    }
}

impl Wrap {
    // Vendor defined mechanisms for Thales AES key wrap.
    const CKM_THALES_AES_KW: u64 = CKM_VENDOR_DEFINED | 0x00000170;
    const CKM_THALES_AES_KWP: u64 = CKM_VENDOR_DEFINED | 0x00000171;

    pub fn mechanism(&self) -> Result<Mechanism> {
        match self {
            Wrap::AesKeyWrap => Ok(Mechanism::AesKeyWrap),
            Wrap::AesKeyWrapPad => Ok(Mechanism::AesKeyWrapPad),
            Wrap::RsaPkcs => Ok(Mechanism::RsaPkcs),
            Wrap::RsaPkcsOaep => Ok(Mechanism::RsaPkcsOaep(PkcsOaepParams::new(
                MechanismType::SHA256,
                PkcsMgfType::MGF1_SHA256,
                PkcsOaepSource::empty(),
            ))),
            Wrap::VendorThalesAesKw => {
                Ok(Mechanism::VendorDefined(VendorDefinedMechanism::new::<()>(
                    MechanismType::new_vendor_defined(Wrap::CKM_THALES_AES_KW)?,
                    None,
                )))
            }
            Wrap::VendorThalesAesKwp => {
                Ok(Mechanism::VendorDefined(VendorDefinedMechanism::new::<()>(
                    MechanismType::new_vendor_defined(Wrap::CKM_THALES_AES_KWP)?,
                    None,
                )))
            }
        }
    }

    pub fn wrapping_key(&self, session: &Session, label: Option<&str>) -> Result<ObjectHandle> {
        let mut attrs = helper::search_spec(None, label)?;
        attrs.push(Attribute::Wrap(true));
        match self {
            Wrap::AesKeyWrap
            | Wrap::AesKeyWrapPad
            | Wrap::VendorThalesAesKw
            | Wrap::VendorThalesAesKwp => {
                attrs.push(Attribute::KeyType(KeyType::Aes.try_into()?));
                attrs.push(Attribute::Class(ObjectClass::SecretKey.try_into()?));
                helper::find_one_object(session, &attrs)
            }
            Wrap::RsaPkcs | Wrap::RsaPkcsOaep => {
                attrs.push(Attribute::KeyType(KeyType::Rsa.try_into()?));
                attrs.push(Attribute::Class(ObjectClass::PublicKey.try_into()?));
                helper::find_one_object(session, &attrs)
            }
        }
    }

    pub fn unwrapping_key(&self, session: &Session, label: Option<&str>) -> Result<ObjectHandle> {
        let mut attrs = helper::search_spec(None, label)?;
        attrs.push(Attribute::Unwrap(true));
        match self {
            Wrap::AesKeyWrap
            | Wrap::AesKeyWrapPad
            | Wrap::VendorThalesAesKw
            | Wrap::VendorThalesAesKwp => {
                attrs.push(Attribute::KeyType(KeyType::Aes.try_into()?));
                attrs.push(Attribute::Class(ObjectClass::SecretKey.try_into()?));
                helper::find_one_object(session, &attrs)
            }
            Wrap::RsaPkcs | Wrap::RsaPkcsOaep => {
                attrs.push(Attribute::KeyType(KeyType::Rsa.try_into()?));
                attrs.push(Attribute::Class(ObjectClass::PrivateKey.try_into()?));
                helper::find_one_object(session, &attrs)
            }
        }
    }

    pub fn check_key(&self, session: &Session, key: ObjectHandle) -> Result<()> {
        let map = AttributeMap::from_object(session, key)?;

        let extractable: bool = map
            .get(&AttributeType::Extractable)
            .ok_or_else(|| HsmError::KeyError("Key does not have an extractable attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if !extractable {
            Err(HsmError::KeyError("Key is not extractable".into()))?;
        }

        let key_type: KeyType = map
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("Key does not have a key type attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        if *self == Wrap::RsaPkcsOaep || *self == Wrap::RsaPkcs {
            let result = match key_type {
                KeyType::Aes => Ok(()),
                KeyType::GenericSecret => Ok(()),
                _ => Err(HsmError::KeyError(format!(
                    "Unsupported key type: {key_type:?}"
                )))?,
            };
            result?;
        }

        Ok(())
    }

    pub fn wrap(
        &self,
        session: &Session,
        key: ObjectHandle,
        wrapping_key_label: Option<&str>,
    ) -> Result<Vec<u8>> {
        self.check_key(session, key)?;
        let wrapping_key = self.wrapping_key(session, wrapping_key_label)?;
        let mechanism = self.mechanism()?;
        Ok(session.wrap_key(&mechanism, wrapping_key, key)?)
    }

    pub fn unwrap(
        &self,
        session: &Session,
        wrapped_key: &[u8],
        wrapping_key_label: Option<&str>,
        template: &AttributeMap,
    ) -> Result<ObjectHandle> {
        let wrapping_key = self.unwrapping_key(session, wrapping_key_label)?;
        let mechanism = self.mechanism()?;
        Ok(session.unwrap_key(
            &mechanism,
            wrapping_key,
            wrapped_key,
            template.to_vec()?.as_slice(),
        )?)
    }
}
