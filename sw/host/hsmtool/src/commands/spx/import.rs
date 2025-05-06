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
use crate::util::attribute::AttrData;
use sphincsplus::{DecodeKey, SpxDomain, SpxPublicKey, SpxSecretKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(short, long)]
    label: String,
    #[arg(
        short,
        long,
        default_value = "None",
        help = "SLH-DSA domain (if the backend requires the domain to be associated with the key)"
    )]
    domain: SpxDomain,
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
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let spx = hsm.spx.as_ref().ok_or(HsmError::SpxUnavailable)?;
        let token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        let sk = SpxSecretKey::read_pem_file(&self.filename)?;
        let pk = SpxPublicKey::from(&sk);

        let key = spx.import_keypair(
            &self.label,
            &sk.algorithm().to_string(),
            self.domain,
            token,
            self.overwrite,
            pk.as_bytes(),
            sk.as_bytes(),
        )?;
        Ok(Box::new(BasicResult {
            success: true,
            id: key.hash.map_or(AttrData::None, AttrData::Str),
            label: AttrData::Str(key.alias),
            value: None,
            error: None,
        }))
    }
}
