// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::any::Any;
use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;

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
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        opentitanlib::test_utils::load_bitstream::LoadBitstream {
            clear_bitstream: false,
            bitstream: Some(self.filename.clone()),
            rom_reset_pulse: self.rom_reset_pulse,
            rom_timeout: self.rom_timeout,
        }
        .init(transport)?;

        Ok(None)
    }
}
