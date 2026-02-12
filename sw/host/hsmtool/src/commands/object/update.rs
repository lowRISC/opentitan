// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;

use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::AttributeMap;
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Update {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Attributes to update.
    attribute: AttributeMap,
}

#[typetag::serde(name = "object-update")]
impl Dispatch for Update {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attr = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        let objects = session.find_objects(&attr)?;
        let _template = self.attribute.to_vec()?;
        bail!(
            "Can't update {:?}; need to update cryptoki to HEAD!",
            objects
        );
        //for object in objects {
        //    session.update_attributes(object, &template)?;
        //}
        //Ok(Box::<BasicResult>::default())
    }
}
