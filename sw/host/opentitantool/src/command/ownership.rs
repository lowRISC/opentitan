// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{File, OpenOptions};
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::helper::OwnershipUnlockParams;

#[derive(Debug, Args)]
pub struct OwnershipUnlockCommand {
    #[command(flatten)]
    params: OwnershipUnlockParams,
    #[arg(short, long, help = "A file containing a binary unlock request")]
    input: Option<PathBuf>,
    #[arg(
        value_name = "FILE",
        help = "A file to write out a binary unlock request"
    )]
    output: Option<PathBuf>,
}

impl CommandDispatch for OwnershipUnlockCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let unlock = self
            .params
            .apply_to(self.input.as_ref().map(File::open).transpose()?.as_mut())?;
        if let Some(output) = &self.output {
            let mut f = OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open(output)?;
            unlock.write(&mut f)?;
        }
        Ok(Some(Box::new(unlock)))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum OwnershipCommand {
    Unlock(OwnershipUnlockCommand),
}
