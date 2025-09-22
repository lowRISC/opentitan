// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::helper;
use crate::util::secret::Secret;
use crate::util::wrap::Wrap;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Wrap the exported key using a wrapping key.
    #[arg(long)]
    wrap: Option<String>,
    #[arg(long, default_value = "rsa-pkcs")]
    wrap_mechanism: Option<Wrap>,
    #[arg(short, long)]
    output: Option<PathBuf>,
}

#[typetag::serde(name = "kdf-export")]
impl Dispatch for Export {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        let object = helper::find_one_object(session, attrs.as_slice())?;

        let secret = Secret::GenericSecret;
        let key = if self.wrap.is_some() {
            secret.wrap_key(
                session,
                object,
                self.wrap.as_deref(),
                self.wrap_mechanism
                    .as_ref()
                    .ok_or(anyhow!("wrap_mechanism is required when wrap is specified"))?,
            )?
        } else {
            secret.export(session, object)?
        };
        if let Some(output) = &self.output {
            helper::write_file(output, key.as_slice())?;
        }
        Ok(Box::<BasicResult>::default())
    }
}
