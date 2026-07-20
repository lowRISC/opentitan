// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;

use crate::commands::Dispatch;
use crate::module::Module;

pub mod generate;
pub mod sign;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum SlhDsa {
    Generate(generate::Generate),
    Sign(sign::Sign),
}

#[typetag::serde(name = "__slh_dsa__")]
impl Dispatch for SlhDsa {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        match self {
            SlhDsa::Generate(x) => x.run(context, hsm, session),
            SlhDsa::Sign(x) => x.run(context, hsm, session),
        }
    }

    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            SlhDsa::Generate(x) => x.leaf(),
            SlhDsa::Sign(x) => x.leaf(),
        }
    }
}
