// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeError, AttributeMap, AttributeType};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Read {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Search spec
    #[arg(short, long)]
    search: Option<AttributeMap>,
    #[arg()]
    output: PathBuf,
}

#[typetag::serde(name = "object-read")]
impl Dispatch for Read {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attr = helper::search_spec_ex(
            self.id.as_deref(),
            self.label.as_deref(),
            self.search.as_ref(),
        )?;
        let object = helper::find_one_object(session, &attr)?;
        let map = AttributeMap::from_object(session, object)?;
        let value = map
            .get(&AttributeType::Value)
            .ok_or(AttributeError::AttributeNotFound(AttributeType::Value))?;
        let value = Vec::<u8>::try_from(value)?;
        let mut result = Box::<BasicResult>::default();
        if self.output.to_str() == Some("-") {
            result.value = Some(String::from_utf8(value)?);
        } else {
            std::fs::write(&self.output, value)?;
        }
        Ok(result)
    }
}
