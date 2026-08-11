// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use anyhow::anyhow;
use core::convert::Into;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;
use std::str::FromStr;

use crate::commands::BasicResult;
use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::helper;
use crate::util::key::slhdsa::{SlhDsaPublicKey, load_private_key, load_public_key};
use crate::util::wrap::{Wrap, WrapPrivateKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// The key is a public key only.
    #[arg(short, long)]
    public: bool,
    /// Attributes to apply to the public key.
    #[arg(long)]
    public_attrs: Option<AttributeMap>,
    /// Attributes to apply to the private key.
    #[arg(long)]
    private_attrs: Option<AttributeMap>,
    /// Unwrap the imported key with a wrapping key.
    #[arg(long)]
    unwrap: Option<String>,
    /// Unwrapping key mechanism. Required when unwrap is specified.
    #[arg(long, default_value = "aes-key-wrap-pad")]
    unwrap_mechanism: Option<WrapPrivateKey>,
    filename: PathBuf,
}

impl Import {
    const PRIVATE_ATTRS: &str = r#"{
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_DECRYPT": false,
        "CKA_SIGN": true,
    }"#;

    const PUBLIC_ATTRS: &str = r#"{
        "CKA_TOKEN": true,
        "CKA_PRIVATE": false,
        "CKA_ENCRYPT": false,
        "CKA_VERIFY": true,
    }"#;

    fn unwrap_key(&self, session: &Session, template: &AttributeMap) -> Result<()> {
        let key = std::fs::read_to_string(&self.filename)?;
        let wrapper: Wrap = self
            .unwrap_mechanism
            .ok_or(anyhow!(
                "unwrap_mechanism is required when wrap is specified"
            ))?
            .into();
        let _key = wrapper.unwrap(session, key.as_bytes(), self.unwrap.as_deref(), template)?;
        Ok(())
    }
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

        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let label = AttrData::Str(self.label.as_ref().cloned().unwrap_or_default());

        let mut public_attrs =
            AttributeMap::from_str(Self::PUBLIC_ATTRS).expect("error in PUBLIC_ATTRS");
        if let Some(tpl) = &self.public_attrs {
            public_attrs.merge(tpl.clone());
        }
        public_attrs.insert(AttributeType::Id, id.clone());
        public_attrs.insert(AttributeType::Label, label.clone());

        let mut private_attrs =
            AttributeMap::from_str(Self::PRIVATE_ATTRS).expect("error in PRIVATE_ATTRS");
        if let Some(tpl) = &self.private_attrs {
            private_attrs.merge(tpl.clone());
        }
        private_attrs.insert(AttributeType::Id, id.clone());
        private_attrs.insert(AttributeType::Label, label.clone());

        if self.public {
            let pk = load_public_key(&self.filename)?;
            public_attrs.merge(pk.into());
            let _pk = session.create_object(&public_attrs.to_vec()?)?;
        } else if self.unwrap.is_some() {
            self.unwrap_key(session, &private_attrs)?;
        } else {
            let sk = load_private_key(&self.filename)?;
            let pk = SlhDsaPublicKey::from(&sk);

            private_attrs.merge(sk.into());
            public_attrs.merge(pk.into());

            let _sk = session.create_object(&private_attrs.to_vec()?)?;
            let _pk = session.create_object(&public_attrs.to_vec()?)?;
        }

        Ok(Box::new(BasicResult {
            success: true,
            id,
            label,
            value: None,
            error: None,
        }))
    }
}
