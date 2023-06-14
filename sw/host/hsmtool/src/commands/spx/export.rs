// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use pem_rfc7468::LineEnding;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use acorn::Acorn;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(short, long)]
    label: String,
    filename: PathBuf,
}

impl Export {
    const PUBLIC_KEY: &'static str = "RAW SPHINCS+ PUBLIC KEY";
    fn export(&self, acorn: &Acorn) -> Result<()> {
        let key = acorn.get_public_key(&self.label)?;
        let pem = pem_rfc7468::encode_string(Self::PUBLIC_KEY, LineEnding::LF, &key)?;
        std::fs::write(&self.filename, &pem)?;
        Ok(())
    }
}

#[typetag::serde(name = "spx-export")]
impl Dispatch for Export {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let acorn = hsm.acorn.as_ref().ok_or(HsmError::AcornUnavailable)?;
        let _token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;
        self.export(acorn)?;
        Ok(Box::<BasicResult>::default())
    }
}
