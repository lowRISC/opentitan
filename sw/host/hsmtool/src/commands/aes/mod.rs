// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;

use crate::commands::Dispatch;
use crate::module::Module;

pub mod export;
pub mod generate;
pub mod import;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Aes {
    Export(export::Export),
    Generate(generate::Generate),
    Import(import::Import),
}

#[typetag::serde(name = "__aes__")]
impl Dispatch for Aes {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        match self {
            Aes::Export(x) => x.run(context, hsm, session),
            Aes::Generate(x) => x.run(context, hsm, session),
            Aes::Import(x) => x.run(context, hsm, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Aes::Export(x) => x.leaf(),
            Aes::Generate(x) => x.leaf(),
            Aes::Import(x) => x.leaf(),
        }
    }
}
