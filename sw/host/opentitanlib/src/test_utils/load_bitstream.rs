// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::path::{Path, PathBuf};

use crate::app::{StagedProgressBar, TransportWrapper};
use crate::io::jtag::JtagParams;
use crate::transport::common::fpga::FpgaProgram;

/// Load a bitstream into the FPGA.
#[derive(Debug, Args)]
pub struct LoadBitstream {
    /// Whether to clear out any existing bitstream.
    #[arg(long)]
    pub clear_bitstream: bool,

    /// The bitstream to load for the test.
    #[arg(long)]
    pub bitstream: Option<PathBuf>,

    /// Load the bitstream, regardless of a matching USR_ACCESS.
    #[arg(long)]
    pub force: bool,
}

impl LoadBitstream {
    pub fn init(&self, transport: &TransportWrapper, jtag_params: &JtagParams) -> Result<()> {
        // Clear out existing bitstream, if requested.
        if self.clear_bitstream {
            log::info!("Clearing bitstream.");
            transport.fpga_ops()?.clear_bitstream()?;
        }
        // Load the specified bitstream, if provided.
        if let Some(bitstream) = &self.bitstream {
            self.load(transport, bitstream, jtag_params)?;
        }

        Ok(())
    }

    pub fn load(
        &self,
        transport: &TransportWrapper,
        file: &Path,
        jtag_params: &JtagParams,
    ) -> Result<()> {
        log::info!("Loading bitstream: {:?}", file);
        let payload = std::fs::read(file)?;
        let progress = StagedProgressBar::new();
        let operation = FpgaProgram {
            bitstream: payload,
            progress: Box::new(progress),
        };

        if !self.force && operation.should_skip(transport, jtag_params)? {
            return Ok(());
        }

        transport
            .fpga_ops()?
            .load_bitstream(&operation.bitstream, &*operation.progress)
    }
}
