// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap};
use crate::util::helper;
use crate::util::secret::Secret;
use crate::util::wrap::Wrap;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long)]
    template: Option<AttributeMap>,
    /// Unwrap the imported key with a wrapping key.
    #[arg(long)]
    unwrap: Option<String>,
    #[arg(long, default_value = "rsa-pkcs")]
    unwrap_mechanism: Option<Wrap>,
    filename: PathBuf,
}

#[typetag::serde(name = "aes-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;

        let result = Box::new(BasicResult {
            success: true,
            id: AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id)),
            label: AttrData::Str(self.label.as_ref().cloned().unwrap_or_default()),
            value: None,
            error: None,
        });

        let secret = Secret::Aes;
        let key = helper::read_file(&self.filename)?;
        if self.unwrap.is_some() {
            let _object = secret.unwrap_key(
                session,
                result.id.clone(),
                result.label.clone(),
                key,
                self.template.clone(),
                self.unwrap.as_deref(),
                self.unwrap_mechanism.as_ref().ok_or(anyhow!(
                    "unwrap_mechanism is required when unwrap is specified"
                ))?,
            )?;
        } else {
            let _object = secret.import(
                session,
                result.id.clone(),
                result.label.clone(),
                key,
                self.template.clone(),
            )?;
        }
        Ok(result)
    }
}
