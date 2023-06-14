// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::{Annotate, Document};
use std::any::Any;
use std::path::PathBuf;
use thiserror::Error;

use crate::commands::{BasicResult, Dispatch};
use crate::module::Module;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Exec {
    file: PathBuf,
}

#[derive(Debug, Serialize)]
pub struct ExecResult {
    pub command: String,
    pub result: Box<dyn Annotate>,
}

#[derive(Debug, Error)]
#[error("Error executing command list: {error:?}")]
pub struct ExecError {
    pub error: anyhow::Error,
    pub result: Document,
}

#[typetag::serde(name = "__exec__")]
impl Dispatch for Exec {
    fn run(
        &self,
        context: &dyn Any,
        hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let commands = std::fs::read_to_string(&self.file)?;
        let commands = serde_annotate::from_str::<Vec<Box<dyn Dispatch>>>(&commands)?;

        // Execute all of the commands, stopping if an error is encountered.
        let mut status = Vec::<ExecResult>::new();
        for command in commands {
            let name = command.typetag_name().to_string();
            log::info!("Executing command {name}");
            match command.run(context, hsm, session) {
                Ok(r) => status.push(ExecResult {
                    command: name,
                    result: r,
                }),
                Err(e) => {
                    status.push(ExecResult {
                        command: name,
                        result: BasicResult::from_error(&e),
                    });
                    return Err(ExecError {
                        error: e,
                        result: serde_annotate::serialize(&status)?,
                    }
                    .into());
                }
            }
        }
        Ok(Box::new(status))
    }
}
