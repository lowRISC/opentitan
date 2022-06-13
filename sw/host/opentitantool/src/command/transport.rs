// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

/// Initialize state of a transport debugger device to fit the device under test.  This
/// typically involves setting pins as input/output, open drain, etc. according to configuration
/// files.
#[derive(Debug, StructOpt)]
pub struct TransportInit {}

impl CommandDispatch for TransportInit {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        // Configure all GPIO pins to default direction and level, according to
        // configuration files provided.
        transport.apply_default_pin_configurations()?;
        Ok(None)
    }
}

/// Commands for interacting with the transport debugger device itself.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum TransportCommand {
    Init(TransportInit),
}
