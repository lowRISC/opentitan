// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fs;
use std::ops::Range;
use std::path::PathBuf;

use crate::commands::{Dispatch, SignResult};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::KeyType;
use crate::util::helper;
use crate::util::signing::{MlDsaDomain, SignData};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Sign {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, default_value = "sha256-hash", help=SignData::HELP)]
    format: SignData,
    /// The ML-DSA domain (pure or pre-hashed).
    #[arg(long, default_value = "pure")]
    domain: MlDsaDomain,
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Update the given byte range in the input file.
    #[arg(short, long, value_parser=helper::parse_range)]
    update_in_place: Option<Range<usize>>,
    input: PathBuf,
}

#[typetag::serde(name = "mldsa-sign")]
impl Dispatch for Sign {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        attrs.push(Attribute::Sign(true));
        let object = helper::find_one_object(session, &attrs)?;

        let data = fs::read(&self.input)?;
        let data = self.format.mldsa_prepare(self.domain, &data)?;
        let mechanism = self.format.mechanism(KeyType::MlDsa)?;
        let result = session.sign(&mechanism, object, &data)?;
        if let Some(output) = &self.output {
            fs::write(output, &result)?;
        }
        if let Some(range) = &self.update_in_place {
            let mut data = fs::read(&self.input)?;
            if let Some(slice) = data.get_mut(range.clone()) {
                slice.copy_from_slice(&result);
            } else {
                return Err(anyhow!("Invalid range on input file: {range:?}"));
            }
            fs::write(&self.input, &data)?;
        }
        Ok(Box::new(SignResult {
            digest: data,
            signature: result,
        }))
    }
}
