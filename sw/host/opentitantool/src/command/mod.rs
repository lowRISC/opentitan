// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod console;
pub mod emulator;
pub mod gpio;
pub mod hello;
pub mod i2c;
pub mod image;
pub mod load_bitstream;
pub mod rsa;
pub mod set_pll;
pub mod spi;
pub mod version;

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, StructOpt)]
/// No Operation.
pub struct NoOp {}

impl CommandDispatch for NoOp {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        Ok(None)
    }
}
