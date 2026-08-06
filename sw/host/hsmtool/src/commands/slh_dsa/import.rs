// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use rsa::pkcs8::DecodePrivateKey;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;
use std::str::FromStr;

use crate::commands::BasicResult;
use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;
use crate::slh_dsa::{SlhDsaPrivateKey, SlhDsaPublicKey};
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, help = "Overwrite an existing key with the same label")]
    overwrite: bool,
    filename: PathBuf,
}

impl Import {
    const PRIVATE_ATTRS: &str = r#"{
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_KEY_TYPE": "CKK_SLH_DSA",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_DECRYPT": false,
        "CKA_SIGN": true,
    }"#;

    const PUBLIC_ATTRS: &str = r#"{
        "CKA_CLASS": "CKO_PUBLIC_KEY",
        "CKA_KEY_TYPE": "CKK_SLH_DSA",
        "CKA_TOKEN": true,
        "CKA_PRIVATE": false,
        "CKA_ENCRYPT": false,
        "CKA_VERIFY": true,
    }"#;
}

#[typetag::serde(name = "slh-dsa-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;

        let data = std::fs::read_to_string(&self.filename)?;
        let sk = SlhDsaPrivateKey::from_pkcs8_pem(&data)?;
        let pk = SlhDsaPublicKey::from(&sk);

        let mut private_attrs =
            AttributeMap::from_str(Self::PRIVATE_ATTRS).expect("error in PRIVATE_ATTRS");
        let mut public_attrs =
            AttributeMap::from_str(Self::PUBLIC_ATTRS).expect("error in PUBLIC_ATTRS");

        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let label = AttrData::Str(self.label.as_ref().cloned().unwrap_or_default());

        private_attrs.insert(AttributeType::Id, id.clone());
        private_attrs.insert(AttributeType::Label, label.clone());
        private_attrs.merge(sk.into());

        public_attrs.insert(AttributeType::Id, id.clone());
        public_attrs.insert(AttributeType::Label, label.clone());
        public_attrs.merge(pk.into());

        let _sk = session.create_object(&private_attrs.to_vec()?)?;
        let _pk = session.create_object(&public_attrs.to_vec()?)?;

        Ok(Box::new(BasicResult {
            success: true,
            id,
            label,
            value: None,
            error: None,
        }))
    }
}
