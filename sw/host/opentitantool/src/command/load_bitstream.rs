// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::transport::cw310;
use opentitanlib::util::rom_detect::RomKind;

/// Load a bitstream into the FPGA.
#[derive(Debug, StructOpt)]
pub struct LoadBitstream {
    #[structopt(name = "FILE")]
    filename: PathBuf,

    #[structopt(
        long,
        possible_values = &RomKind::variants(),
        case_insensitive = true,
        help = "OpenTitan ROM type"
    )]
    pub rom_kind: Option<RomKind>,
    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="50ms", help = "Duration of the reset pulse.")]
    pub rom_reset_pulse: Duration,
    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="1s", help = "Duration of ROM detection timeout")]
    pub rom_timeout: Duration,
}

impl CommandDispatch for LoadBitstream {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        log::info!("Loading bitstream: {:?}", self.filename);
        Ok(transport.dispatch(&cw310::FpgaProgram {
            bitstream: fs::read(&self.filename)?,
            rom_kind: self.rom_kind,
            rom_reset_pulse: self.rom_reset_pulse,
            rom_timeout: self.rom_timeout,
        })?)
    }
}
