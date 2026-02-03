// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::object::ObjectHandle;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::helper;
use crate::util::wrap::{Wrap, WrapPrivateKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Import a private key.
    #[arg(long)]
    private: bool,
    /// Unwrap the imported key with a wrapping key.
    #[arg(long)]
    unwrap: Option<String>,
    // Wrapping key mechanism. Required when unwrap is specified.
    #[arg(long, default_value = "aes-key-wrap-pad")]
    unwrap_mechanism: Option<WrapPrivateKey>,
    /// Template for creating the public key.
    #[arg(long)]
    public_template: Option<AttributeMap>,
    /// Template for creating the private key.
    #[arg(long)]
    private_template: Option<AttributeMap>,
    filename: PathBuf,
}

impl Import {
    const PUBLIC_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PUBLIC_KEY",
        "CKA_KEY_TYPE": "CKK_MLDSA",
        "CKA_TOKEN": true,
        "CKA_VERIFY": true
    }"#;

    const PRIVATE_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_KEY_TYPE": "CKK_MLDSA",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_SIGN": true
    }"#;

    fn import(&self, session: &Session, id: AttrData, label: AttrData) -> Result<ObjectHandle> {
        let data = fs::read(&self.filename)?;
        let key_value = if let Ok((_label, bytes)) = pem_rfc7468::decode_vec(&data) {
            bytes
        } else {
            // Assume DER/Raw
            data
        };

        let mut template = if self.private {
            AttributeMap::from_str(Self::PRIVATE_TEMPLATE).expect("error in PRIVATE_TEMPLATE")
        } else {
            AttributeMap::from_str(Self::PUBLIC_TEMPLATE).expect("error in PUBLIC_TEMPLATE")
        };

        template.insert(AttributeType::Id, id);
        template.insert(AttributeType::Label, label);
        template.insert(AttributeType::Value, AttrData::from(key_value.as_slice()));

        if self.private {
            if let Some(tpl) = &self.private_template {
                template.merge(tpl.clone());
            }
        } else if let Some(tpl) = &self.public_template {
            template.merge(tpl.clone());
        }

        log::info!("template = {}", serde_json::to_string_pretty(&template)?);

        let template_vec = template.to_vec()?;
        Ok(session.create_object(&template_vec)?)
    }

    fn unwrap_key(&self, session: &Session, id: AttrData, label: AttrData) -> Result<ObjectHandle> {
        let wrapper: Wrap = self
            .unwrap_mechanism
            .ok_or(anyhow!(
                "unwrap_mechanism is required when unwrap is specified"
            ))?
            .into();

        let mut template = if self.private {
            AttributeMap::from_str(Self::PRIVATE_TEMPLATE).expect("error in PRIVATE_TEMPLATE")
        } else {
            AttributeMap::from_str(Self::PUBLIC_TEMPLATE).expect("error in PUBLIC_TEMPLATE")
        };
        template.insert(AttributeType::Id, id);
        template.insert(AttributeType::Label, label);

        if self.private {
            if let Some(tpl) = &self.private_template {
                template.merge(tpl.clone());
            }
        } else if let Some(tpl) = &self.public_template {
            template.merge(tpl.clone());
        }

        let wrapped_data = fs::read(&self.filename)?;
        wrapper.unwrap(session, &wrapped_data, self.unwrap.as_deref(), &template)
    }
}

#[typetag::serde(name = "mldsa-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;
        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let label = AttrData::Str(self.label.as_ref().cloned().unwrap_or_default());

        let result = Box::new(BasicResult {
            success: true,
            id: id.clone(),
            label: label.clone(),
            value: None,
            error: None,
        });

        if self.unwrap.is_some() {
            self.unwrap_key(session, id, label)?;
        } else {
            self.import(session, id, label)?;
        }
        Ok(result)
    }
}
