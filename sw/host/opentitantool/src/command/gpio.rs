// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::transport::{Capability, Transport};

#[derive(Debug, StructOpt)]
/// Reads a GPIO pin.
pub struct GpioRead {
    #[structopt(short, long, help = "The GPIO pin to read")]
    pub pin: u32,
}

#[derive(serde::Serialize)]
pub struct GpioReadResult {
    pub pin: u32,
    pub value: bool,
}

impl CommandDispatch for GpioRead {
    fn run(&self, transport: &mut dyn Transport) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities().request(Capability::GPIO).ok()?;
        let gpio = transport.gpio()?;
        let value = gpio.read(self.pin)?;
        Ok(Some(Box::new(GpioReadResult {
            pin: self.pin,
            value: value,
        })))
    }
}

#[derive(Debug, StructOpt)]
/// Writes a GPIO pin.
pub struct GpioWrite {
    #[structopt(short, long, help = "The GPIO pin to write")]
    pub pin: u32,
    #[structopt(short, long, help = "The value to write to the pin")]
    pub value: u8,
}

impl CommandDispatch for GpioWrite {
    fn run(&self, transport: &mut dyn Transport) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities().request(Capability::GPIO).ok()?;
        let gpio = transport.gpio()?;

        gpio.write(self.pin, self.value != 0)?;
        let _value = gpio.read(self.pin)?;
        Ok(None)
    }
}

/// Commands for manipulating GPIO pins.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum GpioCommand {
    Read(GpioRead),
    Write(GpioWrite),
}
