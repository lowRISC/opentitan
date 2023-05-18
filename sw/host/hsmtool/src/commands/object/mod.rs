// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;

use crate::commands::Dispatch;

mod destroy;
mod list;
mod show;
mod update;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Object {
    Destroy(destroy::Destroy),
    List(list::List),
    Show(show::Show),
    Update(update::Update),
}

#[typetag::serde(name = "__object__")]
impl Dispatch for Object {
    fn run(
        &self,
        context: &dyn Any,
        pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        match self {
            Object::Destroy(x) => x.run(context, pkcs11, session),
            Object::List(x) => x.run(context, pkcs11, session),
            Object::Show(x) => x.run(context, pkcs11, session),
            Object::Update(x) => x.run(context, pkcs11, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Object::Destroy(x) => x.leaf(),
            Object::List(x) => x.leaf(),
            Object::Show(x) => x.leaf(),
            Object::Update(x) => x.leaf(),
        }
    }
}
