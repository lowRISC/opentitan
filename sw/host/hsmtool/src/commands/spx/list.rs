// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use sphincsplus::SpxDomain;
use std::any::Any;

use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct List {}

#[derive(Default, Debug, Serialize)]
pub struct Key {
    pub id: String,
    pub label: String,
    pub algorithm: String,
    pub domain: Option<SpxDomain>,
}

#[derive(Default, Debug, Serialize)]
pub struct ListResult {
    version: String,
    objects: Vec<Key>,
}

#[typetag::serde(name = "spx-list")]
impl Dispatch for List {
    fn run(
        &self,
        _context: &dyn Any,
        hsm: &Module,
        _session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let spx = hsm.spx.as_ref().ok_or(HsmError::SpxUnavailable)?;
        let _token = hsm.token.as_deref().ok_or(HsmError::SessionRequired)?;

        let mut result = Box::new(ListResult {
            version: spx.get_version()?,
            ..Default::default()
        });
        let keys = spx.list_keys()?;
        for key in keys {
            let info = spx.get_key_info(&key.alias)?;
            result.objects.push(Key {
                id: info.hash,
                label: key.alias,
                algorithm: info.algorithm,
                domain: info.domain,
            });
        }
        Ok(result)
    }
}
