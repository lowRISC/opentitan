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
pub mod tpm;
pub mod transport;
pub mod update_usr_access;
pub mod version;

use anyhow::Result;
use serde_annotate::Annotate;
use std::any::Any;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, StructOpt)]
/// No Operation.
pub struct NoOp {
    #[structopt(
        short = "d",
        long,
        help = "Delay execution",
        parse(try_from_str = humantime::parse_duration)
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
