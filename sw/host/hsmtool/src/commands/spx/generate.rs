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
use acorn::GenerateFlags;
use sphincsplus::{EncodeKey, SphincsPlus, SpxDomain, SpxSecretKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Generate {
    #[arg(short, long)]
    label: String,
    #[arg(short, long, default_value = "SHA2-128s-simple")]
    algorithm: SphincsPlus,
    #[arg(
        short,
        long,
        default_value = "None",
        help = "SLH-DSA domain (if the backend requires the domain to be associated with the key)"
    )]
    domain: SpxDomain,
    #[arg(short, long, help = "Overwrite an existing key with the same label")]
    overwrite: bool,
    #[arg(short, long, help = "Export the private key material to a file")]
    export: Option<PathBuf>,
}

#[typetag::serde(name = "spx-generate")]
impl Dispatch for Generate {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let spx = hsm.spx.as_ref().ok_or(HsmError::SpxUnavailable)?;
        let token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        #[rustfmt::skip]
        let flags =
            if self.overwrite { GenerateFlags::OVERWRITE } else { GenerateFlags::NONE }
            | if self.export.is_some() { GenerateFlags::EXPORT_PRIVATE } else { GenerateFlags::NONE };

        let key = spx.generate_key(
            &self.label,
            &self.algorithm.to_string(),
            self.domain,
            token,
            flags,
        )?;

        if let Some(path) = &self.export {
            let sk = SpxSecretKey::from_bytes(self.algorithm, &key.private_key)?;
            sk.write_pem_file(path)?;
        }

        Ok(Box::new(BasicResult {
            success: true,
            id: key.hash.map_or(AttrData::None, AttrData::Str),
            label: AttrData::Str(key.alias),
            value: None,
            error: None,
        }))
    }
}
