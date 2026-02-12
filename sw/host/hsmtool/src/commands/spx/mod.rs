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
pub mod list;
pub mod sign;
pub mod verify;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Spx {
    Generate(generate::Generate),
    Export(export::Export),
    Import(import::Import),
    List(list::List),
    Sign(sign::Sign),
    Verify(verify::Verify),
}

#[typetag::serde(name = "__spx__")]
impl Dispatch for Spx {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        match self {
            Spx::Generate(x) => x.run(context, hsm, session),
            Spx::Export(x) => x.run(context, hsm, session),
            Spx::Import(x) => x.run(context, hsm, session),
            Spx::List(x) => x.run(context, hsm, session),
            Spx::Sign(x) => x.run(context, hsm, session),
            Spx::Verify(x) => x.run(context, hsm, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Spx::Generate(x) => x.leaf(),
            Spx::Export(x) => x.leaf(),
            Spx::Import(x) => x.leaf(),
            Spx::List(x) => x.leaf(),
            Spx::Sign(x) => x.leaf(),
            Spx::Verify(x) => x.leaf(),
        }
    }
}
