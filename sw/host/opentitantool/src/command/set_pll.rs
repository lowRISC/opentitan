// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde_annotate::Annotate;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::transport::cw310;

/// Program the CDCE906 PLL chip with defaults.
#[derive(Debug, StructOpt)]
pub struct SetPll {}

impl CommandDispatch for SetPll {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        log::info!("Programming the CDCE906 PLL chip with defaults");
        Ok(transport.dispatch(&cw310::SetPll {})?)
    }
}
