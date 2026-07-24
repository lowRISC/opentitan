// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::KeyType;
use crate::util::helper;
use crate::util::signing::SignData;
use anyhow::Result;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Verify {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, default_value = "plain-text", help=SignData::HELP)]
    format: SignData,
    signature: PathBuf,
    input: PathBuf,
}

#[typetag::serde(name = "slh-dsa-verify")]
impl Dispatch for Verify {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;

        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::SlhDsa.try_into()?));
        attrs.push(Attribute::Verify(true));
        let object = helper::find_one_object(session, &attrs)?;

        let data = helper::read_file(&self.input)?;
        let data = self.format.prepare(KeyType::SlhDsa, &data)?;
        let mechanism = self.format.mechanism(KeyType::SlhDsa)?;
        let signature = helper::read_file(&self.signature)?;

        session.verify(&mechanism, object, &data, &signature)?;
        Ok(Box::<BasicResult>::default())
    }
}
