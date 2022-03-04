// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::transport::Capability;

#[derive(Debug, StructOpt)]
/// Reads a GPIO pin.
pub struct GpioRead {
    #[structopt(name = "PIN", help = "The GPIO pin to read")]
    pub pin: String,
}

#[derive(serde::Serialize)]
pub struct GpioReadResult {
    pub pin: String,
    pub value: bool,
}

impl CommandDispatch for GpioRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        let value = gpio_pin.read()?;
        Ok(Some(Box::new(GpioReadResult {
            pin: self.pin.clone(),
            value,
        })))
    }
}

#[derive(Debug, StructOpt)]
/// Writes a GPIO pin.
pub struct GpioWrite {
    #[structopt(name = "PIN", help = "The GPIO pin to write")]
    pub pin: String,
    #[structopt(
        name = "VALUE",
        parse(try_from_str),
        help = "The value to write to the pin"
    )]
    pub value: bool,
}

impl CommandDispatch for GpioWrite {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;

        gpio_pin.write(self.value)?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt)]
/// Set the I/O mode of a GPIO pin (Input/OpenDrain/PushPull).
pub struct GpioSetMode {
    #[structopt(name = "PIN", help = "The GPIO pin to modify")]
    pub pin: String,
    #[structopt(
        name = "MODE",
        possible_values = &PinMode::variants(),
        case_insensitive=true,
        help = "The I/O mode of the pin"
    )]
    pub mode: PinMode,
}

impl CommandDispatch for GpioSetMode {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        gpio_pin.set_mode(self.mode)?;
        Ok(None)
    }
}

#[derive(Debug, StructOpt)]
/// Set the I/O weak pull mode of a GPIO pin (PullUp/PullDown/None).
pub struct GpioSetPullMode {
    #[structopt(name = "PIN", help = "The GPIO pin to modify")]
    pub pin: String,
    #[structopt(
        name = "PULLMODE",
        possible_values = &PullMode::variants(),
        case_insensitive=true,
        help = "The weak pull mode of the pin"
    )]
    pub pull_mode: PullMode,
}

impl CommandDispatch for GpioSetPullMode {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        gpio_pin.set_pull_mode(self.pull_mode)?;
        Ok(None)
    }
}

/// Commands for manipulating GPIO pins.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum GpioCommand {
    Read(GpioRead),
    Write(GpioWrite),
    SetMode(GpioSetMode),
    SetPullMode(GpioSetPullMode),
}
