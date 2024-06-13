// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod bootstrap;
pub mod certificate;
pub mod clear_bitstream;
pub mod console;
pub mod ecdsa;
pub mod emulator;
pub mod fpga;
pub mod gpio;
pub mod hello;
pub mod i2c;
pub mod image;
pub mod lc;
pub mod load_bitstream;
pub mod otp;
pub mod ownership;
pub mod rescue;
pub mod rsa;
pub mod sam3x;
pub mod set_pll;
pub mod spi;
pub mod spx;
pub mod status_cmd;
pub mod tpm;
pub mod transport;
pub mod update_usr_access;
pub mod version;
pub mod xmodem;

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
    /// Delay execution.
    #[arg(short = 'd', long, value_parser = humantime::parse_duration)]
    delay: Option<Duration>,
    /// Log a string at the `info` level.
    #[arg(long)]
    info: Option<String>,
    /// Log a string at the `error` level.
    #[arg(long)]
    error: Option<String>,
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
        if let Some(info) = &self.info {
            log::info!("{info}");
        }
        if let Some(error) = &self.error {
            log::error!("{error}");
        }
        Ok(None)
    }
}
