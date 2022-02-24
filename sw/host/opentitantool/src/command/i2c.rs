// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use erased_serde::Serialize;
use std::any::Any;
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::i2c::{I2cParams, Transfer};
use opentitanlib::transport::Capability;

/// Read plain data bytes from a I2C device.
#[derive(Debug, StructOpt)]
pub struct I2cRawRead {
    #[structopt(short = "n", long, help = "Number of bytes to read.")]
    length: usize,
}

#[derive(Debug, serde::Serialize)]
pub struct I2cRawReadResponse {
    hexdata: String,
}

impl CommandDispatch for I2cRawRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities().request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport)?;
        let mut v = vec![0u8; self.length];
        i2c_bus.run_transaction(context.addr, &mut [Transfer::Read(&mut v)])?;
        Ok(Some(Box::new(I2cRawReadResponse {
            hexdata: hex::encode(v),
        })))
    }
}

/// Write plain data bytes to a I2C device.
#[derive(Debug, StructOpt)]
pub struct I2cRawWrite {
    #[structopt(short, long, help = "Hex data bytes to write.")]
    hexdata: String,
}

impl CommandDispatch for I2cRawWrite {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        transport.capabilities().request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport)?;
        i2c_bus.run_transaction(
            context.addr,
            &mut [Transfer::Write(&hex::decode(&self.hexdata)?)],
        )?;
        Ok(None)
    }
}

/// Commands for interacting with a generic I2C bus.
#[derive(Debug, StructOpt, CommandDispatch)]
pub enum InternalI2cCommand {
    RawRead(I2cRawRead),
    RawWrite(I2cRawWrite),
}

#[derive(Debug, StructOpt)]
pub struct I2cCommand {
    #[structopt(flatten)]
    params: I2cParams,

    #[structopt(short, long, help = "7-bit address of I2C device (0..0x7F).")]
    addr: u8,

    #[structopt(subcommand)]
    command: InternalI2cCommand,
}

impl CommandDispatch for I2cCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        // None of the I2C commands care about the prior context, but they do
        // care about the `bus` parameter in the current node.
        self.command.run(self, transport)
    }
}
