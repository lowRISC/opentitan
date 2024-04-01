// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::app::{StagedProgressBar, TransportWrapper};
use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};

/// Load a bitstream into the FPGA.
#[derive(Debug, Args)]
pub struct LoadBitstream {
    /// Whether to clear out any existing bitstream.
    #[arg(long)]
    pub clear_bitstream: bool,

    /// The bitstream to load for the test.
    #[arg(long)]
    pub bitstream: Option<PathBuf>,

    /// Duration of the reset pulse.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "50ms")]
    pub rom_reset_pulse: Duration,

    /// Duration of ROM detection timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "2s")]
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
