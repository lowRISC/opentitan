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

pub mod decrypt;
pub mod encrypt;
pub mod export;
pub mod generate;
pub mod import;
pub mod sign;
pub mod verify;

#[derive(clap::Subcommand, Debug, Serialize, Deserialize)]
pub enum Rsa {
    Decrypt(decrypt::Decrypt),
    Encrypt(encrypt::Encrypt),
    Generate(generate::Generate),
    Export(export::Export),
    Import(import::Import),
    Sign(sign::Sign),
    Verify(verify::Verify),
}

#[typetag::serde(name = "__rsa__")]
impl Dispatch for Rsa {
    fn run(
        &self,
        context: &dyn Any,
        pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        match self {
            Rsa::Decrypt(x) => x.run(context, pkcs11, session),
            Rsa::Encrypt(x) => x.run(context, pkcs11, session),
            Rsa::Generate(x) => x.run(context, pkcs11, session),
            Rsa::Export(x) => x.run(context, pkcs11, session),
            Rsa::Import(x) => x.run(context, pkcs11, session),
            Rsa::Sign(x) => x.run(context, pkcs11, session),
            Rsa::Verify(x) => x.run(context, pkcs11, session),
        }
    }
    fn leaf(&self) -> &dyn Dispatch
    where
        Self: Sized,
    {
        match self {
            Rsa::Decrypt(x) => x.leaf(),
            Rsa::Encrypt(x) => x.leaf(),
            Rsa::Generate(x) => x.leaf(),
            Rsa::Export(x) => x.leaf(),
            Rsa::Import(x) => x.leaf(),
            Rsa::Sign(x) => x.leaf(),
            Rsa::Verify(x) => x.leaf(),
        }
    }
}
