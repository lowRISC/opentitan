// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::util::usr_access::{usr_access_set, usr_access_timestamp};

/// Update the USR_ACCESS value of an FPGA bitstream with the current timestamp.
#[derive(Debug, StructOpt)]
pub struct UpdateUsrAccess {
    #[structopt(name = "INPUT_FILE")]
    input: PathBuf,

    #[structopt(name = "OUTPUT_FILE")]
    output: PathBuf,
}

impl CommandDispatch for UpdateUsrAccess {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        let mut bs = fs::read(&self.input)?;
        usr_access_set(&mut bs, usr_access_timestamp())?;
        fs::write(&self.output, bs)?;
        Ok(None)
    }
}
