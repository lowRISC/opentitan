// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::any::Any;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;

/// Clear the bitstream of the FPGA
#[derive(Debug, Args)]
pub struct ClearBitstream {}

impl CommandDispatch for ClearBitstream {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        transport.fpga_ops()?.clear_bitstream()?;
        Ok(None)
    }
}
