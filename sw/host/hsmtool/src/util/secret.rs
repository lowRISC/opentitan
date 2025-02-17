// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This module provides functionality for handling secret keys in an HSM
// (Hardware Security Module). It supports AES and generic secret keys,
// allowing for key generation, import, export, wrapping, and unwrapping.
//
// The `Secret` enum defines the types of secrets supported, and methods are
// provided to manage these keys using the PKCS#11 interface through the
// `cryptoki` crate.

use anyhow::{Ok, Result};
use cryptoki::mechanism::Mechanism;
use cryptoki::object::ObjectHandle;
use cryptoki::session::Session;
use std::str::FromStr;

use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::wrap::Wrap;

pub enum Secret {
    Aes,
    GenericSecret,
}

impl Secret {
    const TEMPLATE_AES: &str = r#"{
        "CKA_CLASS": "CKO_SECRET_KEY",
        "CKA_DERIVE": true,
        "CKA_ENCRYPT": true,
        "CKA_DECRYPT": true,
        "CKA_KEY_TYPE": "CKK_AES",
        "CKA_SENSITIVE": true,
        "CKA_TOKEN": true,
    }"#;

    const TEMPLATE_GENERIC_SECRET: &str = r#"{
        "CKA_CLASS": "CKO_SECRET_KEY",
        "CKA_DERIVE": true,
        "CKA_KEY_TYPE": "CKK_GENERIC_SECRET",
        "CKA_SENSITIVE": true,
        "CKA_TOKEN": true,
    }"#;

    fn key_template(&self) -> Result<AttributeMap> {
        let template = match self {
            Secret::Aes => Self::TEMPLATE_AES,
            Secret::GenericSecret => Self::TEMPLATE_GENERIC_SECRET,
        };
        Ok(AttributeMap::from_str(template).expect("error in TEMPLATE"))
    }

    fn key_type(&self) -> Result<KeyType> {
        match self {
            Secret::Aes => Ok(KeyType::Aes),
            Secret::GenericSecret => Ok(KeyType::GenericSecret),
        }
    }

    fn keygen_mechanism(&self) -> Result<Mechanism> {
        match self {
            Secret::Aes => Ok(Mechanism::AesKeyGen),
            Secret::GenericSecret => Ok(Mechanism::GenericSecretKeyGen),
        }
    }

    fn check(&self, map: &AttributeMap) -> Result<()> {
        let class: ObjectClass = map
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("Key does not have a class attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = map
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("Key does not have a key type attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::SecretKey || key_type != self.key_type()? {
            Err(HsmError::KeyError("Key is not a secret key".into()))?;
        }

        let extractable: bool = map
            .get(&AttributeType::Extractable)
            .ok_or_else(|| HsmError::KeyError("Key does not have an extractable attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if !extractable {
            Err(HsmError::KeyError("Key is not extractable".into()))?;
        }
        Ok(())
    }

    pub fn generate(
        &self,
        session: &Session,
        id: AttrData,
        label: AttrData,
        attrs: Option<AttributeMap>,
    ) -> Result<ObjectHandle> {
        let mut template = self.key_template()?;
        template.insert(AttributeType::Id, id);
        template.insert(AttributeType::Label, label);
        template.insert(AttributeType::ValueLen, 32u64.into());

        if let Some(tpl) = &attrs {
            template.merge(tpl.clone());
        }

        log::info!("template = {}", serde_json::to_string_pretty(&template)?);

        let template = template.to_vec()?;
        Ok(session.generate_key(&self.keygen_mechanism()?, &template)?)
    }

    pub fn import(
        &self,
        session: &Session,
        id: AttrData,
        label: AttrData,
        key: Vec<u8>,
        attrs: Option<AttributeMap>,
    ) -> Result<ObjectHandle> {
        let mut template = self.key_template()?;
        template.insert(AttributeType::Id, id);
        template.insert(AttributeType::Label, label);

        if let Some(tpl) = &attrs {
            template.merge(tpl.clone());
        }

        log::info!("template = {}", serde_json::to_string_pretty(&template)?);

        template.insert(AttributeType::Value, AttrData::from(key.as_slice()));
        let template = template.to_vec()?;
        Ok(session.create_object(&template)?)
    }

    pub fn export(&self, session: &Session, object: ObjectHandle) -> Result<Vec<u8>> {
        let map = AttributeMap::from_object(session, object)?;
        self.check(&map)?;
        let sensitive: bool = map
            .get(&AttributeType::Sensitive)
            .ok_or_else(|| HsmError::KeyError("Key does not have a sensitive attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if sensitive {
            Err(HsmError::KeyError("Key is marked as sensitive".into()))?;
        }

        let key: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Key does not have a value attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        Ok(key)
    }

    pub fn wrap_key(
        &self,
        session: &Session,
        object: ObjectHandle,
        wrap_key_label: Option<&str>,
        wrap_mechanism: &Wrap,
    ) -> Result<Vec<u8>> {
        let map = AttributeMap::from_object(session, object)?;
        self.check(&map)?;
        Ok(wrap_mechanism.wrap(session, object, wrap_key_label)?)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn unwrap_key(
        &self,
        session: &Session,
        id: AttrData,
        label: AttrData,
        key: Vec<u8>,
        attrs: Option<AttributeMap>,
        wrap_key_label: Option<&str>,
        wrap_mechanism: &Wrap,
    ) -> Result<ObjectHandle> {
        let mut template = self.key_template()?;
        template.insert(AttributeType::Id, id);
        template.insert(AttributeType::Label, label);

        if let Some(tpl) = &attrs {
            template.merge(tpl.clone());
        }

        log::info!("template = {}", serde_json::to_string_pretty(&template)?);
        Ok(wrap_mechanism.unwrap(session, key.as_slice(), wrap_key_label, &template)?)
    }
}
