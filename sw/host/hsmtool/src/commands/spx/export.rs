// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;
use std::str::FromStr;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use acorn::SpxInterface;
use sphincsplus::{EncodeKey, SphincsPlus, SpxPublicKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(short, long)]
    label: String,
    filename: PathBuf,
}

impl Export {
    fn export(&self, acorn: &dyn SpxInterface) -> Result<()> {
        let key = acorn.get_key_info(&self.label)?;
        let algorithm = SphincsPlus::from_str(&key.algorithm)?;
        let pk = SpxPublicKey::from_bytes(algorithm, &key.public_key)?;
        pk.write_pem_file(&self.filename)?;
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
        let acorn = hsm.acorn.as_deref().ok_or(HsmError::AcornUnavailable)?;
        let _token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;
        self.export(acorn)?;
        Ok(Box::<BasicResult>::default())
    }
}
