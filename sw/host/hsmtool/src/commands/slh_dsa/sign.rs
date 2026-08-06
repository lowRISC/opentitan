// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use sphincsplus::SpxDomain;
use std::any::Any;
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
    #[arg(short, long, default_value = "plain-text", help=SignData::HELP)]
    format: SignData,
    #[arg(short = 'd', long, default_value = "pure")]
    domain: SpxDomain,
    #[arg(short, long)]
    output: PathBuf,
    input: PathBuf,
}

#[typetag::serde(name = "slh-dsa-sign")]
impl Dispatch for Sign {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;

        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::SlhDsa.try_into()?));
        attrs.push(Attribute::Sign(true));
        let object = helper::find_one_object(session, &attrs)?;

        let data = helper::read_file(&self.input)?;
        let data = self.format.spx_prepare(self.domain, &data)?;
        let mechanism = self.domain.slh_dsa_mechanism();

        let result = session.sign(&mechanism, object, &data)?;
        helper::write_file(&self.output, &result)?;
        Ok(Box::new(SignResult {
            digest: data,
            signature: result,
        }))
    }
}
