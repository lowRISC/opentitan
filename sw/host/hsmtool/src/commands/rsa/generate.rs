// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::mechanism::Mechanism;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
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
    #[arg(short = 'n', long, default_value = "3072")]
    key_length: u64,
    #[arg(short = 'e', long, default_value = "65537")]
    public_exponent: u64,
    #[arg(
        long,
        help = "Permit the generated key to be used for wrapping other keys"
    )]
    wrapping: bool,
    #[arg(long, help = "Permit the generated key to be extractable")]
    extractable: bool,
    #[arg(long, help = "Template for creating the public key")]
    public_template: Option<AttributeMap>,
    #[arg(long, help = "Template for creating the private key")]
    private_template: Option<AttributeMap>,
}

impl Generate {
    const PUBLIC_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PUBLIC_KEY",
        "CKA_TOKEN": true,
        "CKA_ENCRYPT": true,
        "CKA_VERIFY": true
    }"#;

    const PRIVATE_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_DECRYPT": true,
        "CKA_SIGN": true
    }"#;
}

#[typetag::serde(name = "rsa-generate")]
impl Dispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;
        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let result = Box::new(BasicResult {
            success: true,
            id: id.clone(),
            label: AttrData::Str(self.label.as_ref().cloned().unwrap_or_default()),
            error: None,
        });

        let mut public_template =
            AttributeMap::from_str(Self::PUBLIC_TEMPLATE).expect("error in PUBLIC_TEMPLATE");
        let mut private_template =
            AttributeMap::from_str(Self::PRIVATE_TEMPLATE).expect("error in PRIVATE_TEMPLATE");
        public_template.insert(AttributeType::Id, id.clone());
        public_template.insert(AttributeType::Label, result.label.clone());
        public_template.insert(AttributeType::ModulusBits, AttrData::from(self.key_length));
        public_template.insert(
            AttributeType::PublicExponent,
            AttrData::from(self.public_exponent.to_be_bytes().as_slice()),
        );
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
            &Mechanism::RsaPkcsKeyPairGen,
            &public_template,
            &private_template,
        )?;
        Ok(result)
    }
}
