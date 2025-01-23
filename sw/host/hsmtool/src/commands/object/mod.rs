// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;

use crate::commands::Dispatch;
use crate::module::Module;

mod destroy;
mod list;
mod read;
mod show;
mod update;
mod write;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Object {
    Destroy(destroy::Destroy),
    List(list::List),
    Read(read::Read),
    Show(show::Show),
    Update(update::Update),
    Write(write::Write),
}

#[typetag::serde(name = "__object__")]
impl Dispatch for Object {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        match self {
            Object::Destroy(x) => x.run(context, hsm, session),
            Object::List(x) => x.run(context, hsm, session),
            Object::Read(x) => x.run(context, hsm, session),
            Object::Show(x) => x.run(context, hsm, session),
            Object::Update(x) => x.run(context, hsm, session),
            Object::Write(x) => x.run(context, hsm, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Object::Destroy(x) => x.leaf(),
            Object::List(x) => x.leaf(),
            Object::Read(x) => x.leaf(),
            Object::Show(x) => x.leaf(),
            Object::Update(x) => x.leaf(),
            Object::Write(x) => x.leaf(),
        }
    }
}
