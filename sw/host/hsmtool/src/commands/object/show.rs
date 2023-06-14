// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::AttributeMap;
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Show {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
}

#[derive(Default, Debug, Serialize, Deserialize)]
pub struct ShowResult {
    pub objects: Vec<AttributeMap>,
}

#[typetag::serde(name = "object-show")]
impl Dispatch for Show {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attr = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        let objects = session.find_objects(&attr)?;
        let mut result = Box::<ShowResult>::default();
        for object in objects {
            let map = AttributeMap::from_object(session, object)?;
            result.objects.push(map);
        }
        Ok(result)
    }
}
