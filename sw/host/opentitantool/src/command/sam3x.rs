// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::any::Any;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;

/// Resets the SAM3X chip on the Chip Whisperer FPGA board.
#[derive(Debug, Args)]
pub struct Reset {}

impl CommandDispatch for Reset {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        log::info!("Resetting the SAM3X chip");
        transport.dispatch(&ot_transport_chipwhisperer::ResetSam3x {})
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
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        transport.dispatch(&ot_transport_chipwhisperer::GetSam3xFwVersion {})
    }
}
