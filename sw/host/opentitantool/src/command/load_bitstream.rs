// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::any::Any;
use std::path::PathBuf;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::io::jtag::JtagParams;

/// Load a bitstream into the FPGA.
#[derive(Debug, Args)]
pub struct LoadBitstream {
    #[arg(value_name = "FILE")]
    filename: PathBuf,

    /// Load the bitstream, regardless of a matching USR_ACCESS.
    #[arg(long)]
    pub force: bool,

    /// JTAG options used to check the FPGA's currently loaded bitstream via the backdoor TAP.
    #[command(flatten)]
    pub jtag_params: JtagParams,
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
            force: self.force,
        }
        .init(transport, &self.jtag_params)?;

        Ok(None)
    }
}
