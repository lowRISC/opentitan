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

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::KeyType;
use crate::util::helper;
use crate::util::signing::{MlDsaDomain, SignData};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Verify {
    /// Unique identifier of the key to use for verification.
    #[arg(long)]
    id: Option<String>,
    /// Label of the key to use for verification.
    #[arg(short, long)]
    label: Option<String>,
    /// Format of the input data.
    #[arg(short, long, default_value = "sha256-hash", help=SignData::HELP)]
    format: SignData,
    /// The ML-DSA domain (pure or pre-hashed).
    #[arg(long, default_value = "pure")]
    domain: MlDsaDomain,
    /// The signature is at the given byte range of the input file.
    #[arg(short, long, value_parser=helper::parse_range, conflicts_with="signature")]
    signature_at: Option<Range<usize>>,
    /// Path to the file containing the data to be verified.
    input: PathBuf,
    /// Path to the file containing the signature.
    #[arg(conflicts_with = "signature_at")]
    signature: Option<PathBuf>,
}

#[typetag::serde(name = "mldsa-verify")]
impl Dispatch for Verify {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        attrs.push(Attribute::Verify(true));
        let object = helper::find_one_object(session, &attrs)?;

        let data = fs::read(&self.input)?;
        // TODO: decide whether domain preparation should be done in this program or if the HSM is expected to do it.
        let data = self.format.mldsa_prepare(self.domain, &data)?;
        let mechanism = self.format.mechanism(KeyType::MlDsa)?;
        let signature = if let Some(filename) = &self.signature {
            fs::read(filename)?
        } else if let Some(range) = &self.signature_at {
            let input = fs::read(&self.input)?;
            input
                .get(range.clone())
                .ok_or_else(|| anyhow!("Invalid range on input file: {range:?}"))?
                .to_vec()
        } else {
            unreachable!();
        };
        session.verify(&mechanism, object, &data, &signature)?;
        Ok(Box::<BasicResult>::default())
    }
}
