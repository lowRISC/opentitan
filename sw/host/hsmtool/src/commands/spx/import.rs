// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::AttrData;
use sphincsplus::{DecodeKey, SpxPublicKey, SpxSecretKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(short, long)]
    label: String,
    #[arg(short, long, help = "Overwrite an existing key with the same label")]
    overwrite: bool,
    filename: PathBuf,
}

#[typetag::serde(name = "spx-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let acorn = hsm.acorn.as_ref().ok_or(HsmError::AcornUnavailable)?;
        let token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        let sk = SpxSecretKey::read_pem_file(&self.filename)?;
        let pk = SpxPublicKey::from(&sk);

        let key = acorn.import_keypair(
            &self.label,
            &sk.algorithm().to_string(),
            token,
            self.overwrite,
            pk.as_bytes(),
            sk.as_bytes(),
        )?;
        Ok(Box::new(BasicResult {
            success: true,
            id: AttrData::Str(key.hash.expect("key hash")),
            label: AttrData::Str(key.alias),
            error: None,
        }))
    }
}
