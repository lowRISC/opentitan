// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use std::any::Any;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::transport::chip_whisperer;

/// Program the CDCE906 PLL chip with defaults.
#[derive(Debug, Args)]
pub struct SetPll {}

impl CommandDispatch for SetPll {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        log::info!("Programming the CDCE906 PLL chip with defaults");
        transport.dispatch(&chip_whisperer::SetPll {})
    }
}
