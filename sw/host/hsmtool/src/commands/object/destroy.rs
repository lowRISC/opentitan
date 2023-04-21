// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Destroy {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
}

#[typetag::serde(name = "object-destroy")]
impl Dispatch for Destroy {
    fn run(
        &self,
        _context: &dyn Any,
        _pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attr = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        let objects = session.find_objects(&attr)?;
        log::info!("Destroying {} objects", objects.len());
        for object in objects {
            session.destroy_object(object)?;
        }
        Ok(Box::<BasicResult>::default())
    }
}
