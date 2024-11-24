// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use sphincsplus::SpxDomain;
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::helper;
use crate::util::signing::SignData;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Sign {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, default_value = "plain-text", help=SignData::HELP)]
    format: SignData,
    /// Reverse the input data (for little-endian targets).
    #[arg(short = 'r', long)]
    little_endian: bool,
    /// The SPHINCS+ signing domain.
    #[arg(short = 'd', long, default_value = "pure")]
    domain: SpxDomain,
    #[arg(short, long)]
    output: PathBuf,
    input: PathBuf,
}

#[typetag::serde(name = "spx-sign")]
impl Dispatch for Sign {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let acorn = hsm.acorn.as_ref().ok_or(HsmError::AcornUnavailable)?;
        let _token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        let data = helper::read_file(&self.input)?;
        let data = self
            .format
            .spx_prepare(self.domain, &data, self.little_endian)?;
        let result = acorn.sign(self.label.as_deref(), self.id.as_deref(), &data)?;
        helper::write_file(&self.output, &result)?;
        Ok(Box::<BasicResult>::default())
    }
}
