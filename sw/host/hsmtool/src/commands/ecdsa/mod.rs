// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::Dispatch;
use crate::module::Module;

pub mod export;
pub mod generate;
pub mod import;
pub mod sign;
pub mod verify;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Ecdsa {
    Generate(generate::Generate),
    Export(export::Export),
    Import(import::Import),
    Sign(sign::Sign),
    Verify(verify::Verify),
}

#[typetag::serde(name = "__ecdsa__")]
impl Dispatch for Ecdsa {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        match self {
            Ecdsa::Generate(x) => x.run(context, hsm, session),
            Ecdsa::Export(x) => x.run(context, hsm, session),
            Ecdsa::Import(x) => x.run(context, hsm, session),
            Ecdsa::Sign(x) => x.run(context, hsm, session),
            Ecdsa::Verify(x) => x.run(context, hsm, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Ecdsa::Generate(x) => x.leaf(),
            Ecdsa::Export(x) => x.leaf(),
            Ecdsa::Import(x) => x.leaf(),
            Ecdsa::Sign(x) => x.leaf(),
            Ecdsa::Verify(x) => x.leaf(),
        }
    }
}
