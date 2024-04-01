// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::{StagedProgressBar, TransportWrapper};
use opentitanlib::transport::common::fpga::FpgaProgram;

/// Load a bitstream into the FPGA.
#[derive(Debug, Args)]
pub struct LoadBitstream {
    #[arg(value_name = "FILE")]
    filename: PathBuf,

    /// Duration of the reset pulse.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "50ms")]
    pub rom_reset_pulse: Duration,
    /// Duration of ROM detection timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "2s")]
    pub rom_timeout: Duration,
}

impl CommandDispatch for LoadBitstream {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        log::info!("Loading bitstream: {:?}", self.filename);
        let bitstream = fs::read(&self.filename)?;
        let progress = StagedProgressBar::new();
        let operation = FpgaProgram {
            bitstream,
            rom_reset_pulse: self.rom_reset_pulse,
            rom_timeout: self.rom_timeout,
            progress: Box::new(progress),
        };

        if operation.should_skip(transport)? {
            return Ok(None);
        }
        transport.dispatch(&operation)
    }
}
