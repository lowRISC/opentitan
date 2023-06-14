// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::KeyType;
use crate::util::helper;
use crate::util::signing::SignData;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Sign {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, value_enum, default_value = "sha256-hash")]
    format: SignData,
    #[arg(
        short = 'r',
        long,
        help = "Reverse the input data and result (for little-endian targets)"
    )]
    little_endian: bool,
    #[arg(short, long)]
    output: Option<PathBuf>,
    input: PathBuf,
}

#[typetag::serde(name = "rsa-sign")]
impl Dispatch for Sign {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::Rsa.try_into()?));
        attrs.push(Attribute::Sign(true));
        let object = helper::find_one_object(session, &attrs)?;

        let mut data = helper::read_file(&self.input)?;
        if self.little_endian {
            data.reverse();
        }
        let data = self.format.prepare(&data)?;
        let mechanism = self.format.mechanism()?;
        let mut result = session.sign(&mechanism, object, &data)?;
        if self.little_endian {
            result.reverse();
        }
        if let Some(output) = &self.output {
            helper::write_file(output, &result)?;
        }
        Ok(Box::<BasicResult>::default())
    }
}
