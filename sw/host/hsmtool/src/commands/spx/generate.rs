// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::AttrData;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Generate {
    #[arg(short, long)]
    label: String,
    #[arg(short, long, default_value = "SPHINCS+-SHAKE256-128s-simple")]
    algorithm: String,
    #[arg(short, long, help = "Overwrite an existing key with the same label")]
    overwrite: bool,
}

#[typetag::serde(name = "spx-generate")]
impl Dispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let acorn = hsm.acorn.as_ref().ok_or(HsmError::AcornUnavailable)?;
        let token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        let key = acorn.generate_key(&self.label, &self.algorithm, token, self.overwrite)?;

        Ok(Box::new(BasicResult {
            success: true,
            id: AttrData::Str(key.hash.expect("key hash")),
            label: AttrData::Str(key.alias),
            error: None,
        }))
    }
}
