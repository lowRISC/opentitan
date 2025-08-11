// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::mechanism::Mechanism;
use cryptoki::session::Session;
use p256::elliptic_curve::pkcs8;
use p256::elliptic_curve::pkcs8::der::Encode;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::str::FromStr;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Generate {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long, default_value = "1.2.840.10045.3.1.7")]
    curve: String,
    #[arg(long)]
    wrapping: bool,
    /// Permit the generated key to be extractable.
    #[arg(long)]
    extractable: bool,
    /// Template for creating the public key.
    #[arg(long)]
    public_template: Option<AttributeMap>,
    /// Template for creating the private key.
    #[arg(long)]
    private_template: Option<AttributeMap>,
}

impl Generate {
    const PUBLIC_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PUBLIC_KEY",
        "CKA_KEY_TYPE": "CKK_EC",
        "CKA_TOKEN": true,
        "CKA_VERIFY": true
    }"#;

    const PRIVATE_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_KEY_TYPE": "CKK_EC",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_SIGN": true
    }"#;
}

#[typetag::serde(name = "ecdsa-generate")]
impl Dispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;
        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let result = Box::new(BasicResult {
            success: true,
            id: id.clone(),
            label: AttrData::Str(self.label.as_ref().cloned().unwrap_or_default()),
            value: None,
            error: None,
        });

        let curve = pkcs8::ObjectIdentifier::new(&self.curve)?.to_der()?;
        let mut public_template =
            AttributeMap::from_str(Self::PUBLIC_TEMPLATE).expect("error in PUBLIC_TEMPLATE");
        let mut private_template =
            AttributeMap::from_str(Self::PRIVATE_TEMPLATE).expect("error in PRIVATE_TEMPLATE");
        public_template.insert(AttributeType::Id, id.clone());
        public_template.insert(AttributeType::Label, result.label.clone());
        public_template.insert(AttributeType::EcParams, AttrData::from(curve.as_slice()));

        if let Some(tpl) = &self.public_template {
            public_template.merge(tpl.clone());
        }

        private_template.insert(AttributeType::Id, id);
        private_template.insert(AttributeType::Label, result.label.clone());
        if let Some(tpl) = &self.private_template {
            private_template.merge(tpl.clone());
        }

        if self.wrapping {
            public_template.insert(AttributeType::Wrap, AttrData::from(true));
            private_template.insert(AttributeType::Unwrap, AttrData::from(true));
        }
        if self.extractable {
            public_template.insert(AttributeType::Extractable, AttrData::from(true));
            private_template.insert(AttributeType::Extractable, AttrData::from(true));
        }

        log::info!(
            "public_template = {}",
            serde_json::to_string_pretty(&public_template)?
        );
        log::info!(
            "private_template = {}",
            serde_json::to_string_pretty(&private_template)?
        );

        let public_template = public_template.to_vec()?;
        let private_template = private_template.to_vec()?;
        let (_pubkey, _privkey) = session.generate_key_pair(
            &Mechanism::EccKeyPairGen,
            &public_template,
            &private_template,
        )?;
        Ok(result)
    }
}
