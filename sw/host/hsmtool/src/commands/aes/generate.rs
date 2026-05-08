// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap};
use crate::util::helper;
use crate::util::secret::Secret;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Generate {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long)]
    template: Option<AttributeMap>,
}

#[typetag::serde(name = "aes-generate")]
impl Dispatch for Generate {
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
        let _key = secret.generate(
            session,
            result.id.clone(),
            result.label.clone(),
            self.template.clone(),
        )?;
        Ok(result)
    }
}
