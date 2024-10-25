// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::ops::Range;
use std::path::PathBuf;

use crate::commands::{Dispatch, SignResult};
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
    #[arg(short, long, default_value = "sha256-hash", help=SignData::HELP)]
    format: SignData,
    /// Reverse the input data and result (for little-endian targets).
    #[arg(short = 'r', long)]
    little_endian: bool,
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Update the given byte range in the input file.
    #[arg(short, long, value_parser=helper::parse_range)]
    update_in_place: Option<Range<usize>>,
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
        let data = self.format.prepare(KeyType::Rsa, &data)?;
        let mechanism = self.format.mechanism(KeyType::Rsa)?;
        let mut result = session.sign(&mechanism, object, &data)?;
        if self.little_endian {
            result.reverse();
        }
        if let Some(output) = &self.output {
            helper::write_file(output, &result)?;
        }
        if let Some(range) = &self.update_in_place {
            let mut data = helper::read_file(&self.input)?;
            if let Some(slice) = data.get_mut(range.clone()) {
                slice.copy_from_slice(&result);
            } else {
                return Err(anyhow!("Invalid range on input file: {range:?}"));
            }
            helper::write_file(&self.input, &data)?;
        }
        Ok(Box::new(SignResult {
            digest: data,
            signature: result,
        }))
    }
}
