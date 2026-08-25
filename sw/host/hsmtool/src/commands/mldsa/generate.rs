// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::mechanism::Mechanism;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::str::FromStr;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Generate {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, default_value = "mldsa-87")]
    parameter_set: MldsaParameterSet,
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
        "CKA_TOKEN": true,
        "CKA_ENCRYPT": false,
        "CKA_VERIFY": true,
        "CKA_PRIVATE": false,
    }"#;

    const PRIVATE_TEMPLATE: &str = r#"{
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_DECRYPT": false,
        "CKA_SIGN": true,
    }"#;
}

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    num_enum::IntoPrimitive,
    clap::ValueEnum,
    serde::Serialize,
    serde::Deserialize,
)]
#[repr(u64)]
pub enum MldsaParameterSet {
    #[serde(rename = "CKP_ML_DSA_44")]
    #[value(name = "mldsa-44", alias = "mldsa44", alias = "44")]
    Mldsa44 = cryptoki_sys::CKP_ML_DSA_44,
    #[serde(rename = "CKP_ML_DSA_65")]
    #[value(name = "mldsa-65", alias = "mldsa65", alias = "65")]
    Mldsa65 = cryptoki_sys::CKP_ML_DSA_65,
    #[serde(rename = "CKP_ML_DSA_87")]
    #[value(name = "mldsa-87", alias = "mldsa87", alias = "87")]
    Mldsa87 = cryptoki_sys::CKP_ML_DSA_87,
}

impl From<MldsaParameterSet> for AttrData {
    fn from(val: MldsaParameterSet) -> Self {
        AttrData::Ulong(val.into())
    }
}

#[typetag::serde(name = "mldsa-generate")]
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

        let mut public_template =
            AttributeMap::from_str(Self::PUBLIC_TEMPLATE).expect("error in PUBLIC_TEMPLATE");
        public_template.insert(AttributeType::ParameterSet, self.parameter_set.into());
        public_template.insert(AttributeType::Id, id.clone());
        public_template.insert(AttributeType::Label, result.label.clone());
        public_template.insert(AttributeType::KeyType, KeyType::MlDsa.into());
        if let Some(tpl) = &self.public_template {
            public_template.merge(tpl.clone());
        }

        let mut private_template =
            AttributeMap::from_str(Self::PRIVATE_TEMPLATE).expect("error in PRIVATE_TEMPLATE");
        private_template.insert(AttributeType::Id, id);
        private_template.insert(AttributeType::Label, result.label.clone());
        private_template.insert(AttributeType::KeyType, KeyType::MlDsa.into());
        if let Some(tpl) = &self.private_template {
            private_template.merge(tpl.clone());
        }

        private_template.insert(AttributeType::Extractable, AttrData::from(self.extractable));

        log::debug!(
            "public_template = {}",
            serde_json::to_string_pretty(&public_template)?
        );
        log::debug!(
            "private_template = {}",
            serde_json::to_string_pretty(&private_template)?
        );

        let public_template = public_template.to_vec()?;
        let private_template = private_template.to_vec()?;
        let (_pubkey, _privkey) = session.generate_key_pair(
            &Mechanism::MlDsaKeyPairGen,
            &public_template,
            &private_template,
        )?;
        Ok(result)
    }
}
