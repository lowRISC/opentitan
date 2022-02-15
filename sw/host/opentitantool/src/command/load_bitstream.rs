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
use opentitanlib::transport::cw310;

/// Read data from a SPI EEPROM.
#[derive(Debug, StructOpt)]
pub struct LoadBitstream {
    #[structopt(name = "FILE")]
    filename: PathBuf,
}

impl CommandDispatch for LoadBitstream {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        Ok(transport.dispatch(&cw310::FpgaProgram {
            bitstream: fs::read(&self.filename)?,
        })?)
    }
}
