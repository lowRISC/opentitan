// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::transport::chip_whisperer;

/// Resets the SAM3X chip on the Chip Whisperer FPGA board.
#[derive(Debug, Args)]
pub struct Reset {}

impl CommandDispatch for Reset {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        log::info!("Resetting the SAM3X chip");
        transport.dispatch(&chip_whisperer::ResetSam3x {})
    }
}

/// Gets the SAM3X firmware version on the Chip Whisperer FPGA board.
#[derive(Debug, Args)]
pub struct GetFwVersion {}

impl CommandDispatch for GetFwVersion {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.dispatch(&chip_whisperer::GetSam3xFwVersion {})
    }
}
