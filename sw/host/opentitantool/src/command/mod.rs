// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod clear_bitstream;
pub mod console;
pub mod emulator;
pub mod fpga;
pub mod gpio;
pub mod hello;
pub mod i2c;
pub mod image;
pub mod load_bitstream;
pub mod otp;
pub mod reset_sam3x;
pub mod rsa;
pub mod set_pll;
pub mod spi;
pub mod spx;
pub mod status_cmd;
pub mod tpm;
pub mod transport;
pub mod update_usr_access;
pub mod version;

use anyhow::Result;
use clap::Args;
use serde_annotate::Annotate;
use std::any::Any;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, Args)]
/// No Operation.
pub struct NoOp {
    #[arg(
        short = 'd',
        long,
        help = "Delay execution",
        value_parser = humantime::parse_duration
    )]
    delay: Option<Duration>,
}

impl CommandDispatch for NoOp {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(d) = self.delay {
            std::thread::sleep(d);
        }
        Ok(None)
    }
}
