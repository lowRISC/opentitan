// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use anyhow::{Result, bail};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long)]
    attributes: Option<AttributeMap>,
    /// Unwrap the imported key with a wrapping key.
    #[arg(long)]
    unwrap: Option<String>,
    filename: PathBuf,
}

impl Import {
    const ATTRIBUTES: &'static str = r#"{
        "CKA_TOKEN": true,
        "CKA_CLASS": "CKO_SECRET_KEY",
        "CKA_KEY_TYPE": "CKK_GENERIC_SECRET",
        "CKA_DERIVE": true,
    }"#;

    fn unwrap_key(&self, _session: &Session, _template: &AttributeMap) -> Result<()> {
        bail!("Kdf key import by unwrapping is not supported yet!");
    }
}

#[typetag::serde(name = "kdf-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;

        let mut attributes = AttributeMap::from_str(Self::ATTRIBUTES).expect("error in ATTRIBUTES");
        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let result = Box::new(BasicResult {
            success: true,
            id: id.clone(),
            label: AttrData::Str(self.label.as_ref().cloned().unwrap_or_default()),
            value: None,
            error: None,
        });

        attributes.insert(AttributeType::Id, id.clone());
        attributes.insert(AttributeType::Label, result.label.clone());
        if let Some(tpl) = &self.attributes {
            attributes.merge(tpl.clone());
        }

        if self.unwrap.is_some() {
            self.unwrap_key(session, &attributes)?;
        } else {
            let key = fs::read(&self.filename)?;
            attributes.insert(AttributeType::Value, AttrData::from(key.as_slice()));
            let _secretkey = session.create_object(&attributes.to_vec()?)?;
        }
        Ok(result)
    }
}
