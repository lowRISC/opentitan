// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::path::{Path, PathBuf};
use std::time::Duration;
use structopt::StructOpt;

use crate::app::{StagedProgressBar, TransportWrapper};
use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};
use crate::util::rom_detect::RomKind;

/// Load a bitstream into the FPGA.
#[derive(Debug, StructOpt)]
pub struct LoadBitstream {
    #[structopt(long, help = "Whether to clear out any existing bitstream.")]
    pub clear_bitstream: bool,

    #[structopt(long, help = "The bitstream to load for the test")]
    pub bitstream: Option<PathBuf>,

    #[structopt(
        long,
        possible_values = &RomKind::variants(),
        case_insensitive = true,
        help = "OpenTitan ROM type"
    )]
    pub rom_kind: Option<RomKind>,

    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="50ms", help = "Duration of the reset pulse.")]
    pub rom_reset_pulse: Duration,

    #[structopt(long, parse(try_from_str=humantime::parse_duration), default_value="2s", help = "Duration of ROM detection timeout")]
    pub rom_timeout: Duration,
}

impl LoadBitstream {
    pub fn init(&self, transport: &TransportWrapper) -> Result<Option<Box<dyn Annotate>>> {
        // Clear out existing bitstream, if requested.
        if self.clear_bitstream {
            log::info!("Clearing bitstream.");
            transport.dispatch(&ClearBitstream)?;
        }
        // Load the specified bitstream, if provided.
        if let Some(bitstream) = &self.bitstream {
            self.load(transport, bitstream)
        } else {
            Ok(None)
        }
    }

    pub fn load(
        &self,
        transport: &TransportWrapper,
        file: &Path,
    ) -> Result<Option<Box<dyn Annotate>>> {
        log::info!("Loading bitstream: {:?}", file);
        let payload = std::fs::read(file)?;
        let progress = StagedProgressBar::new();
        let operation = FpgaProgram {
            bitstream: payload,
            rom_kind: self.rom_kind,
            rom_reset_pulse: self.rom_reset_pulse,
            rom_timeout: self.rom_timeout,
            progress: Box::new(progress),
        };
        transport.dispatch(&operation)
    }
}
