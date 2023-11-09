// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde_annotate::Annotate;
use std::any::Any;
use std::convert::From;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::i2c::{self, DeviceStatus, I2cParams, Transfer};
use opentitanlib::tpm;
use opentitanlib::transport::Capability;
use opentitanlib::util::parse_int::ParseInt;

/// Read plain data bytes from a I2C device.
#[derive(Debug, Args)]
pub struct I2cRawRead {
    /// Number of bytes to read.
    #[arg(short = 'n', long, value_parser = usize::from_str)]
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
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        let mut v = vec![0u8; self.length];
        i2c_bus.run_transaction(None, &mut [Transfer::Read(&mut v)])?;
        Ok(Some(Box::new(I2cRawReadResponse {
            hexdata: hex::encode(v),
        })))
    }
}

/// Write plain data bytes to a I2C device.
#[derive(Debug, Args)]
pub struct I2cRawWrite {
    /// Hex data bytes to write.
    #[arg(short = 'd', long)]
    hexdata: String,
}

impl CommandDispatch for I2cRawWrite {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        i2c_bus.run_transaction(None, &mut [Transfer::Write(&hex::decode(&self.hexdata)?)])?;
        Ok(None)
    }
}

/// Write data bytes to a I2C device, then read back a response.
#[derive(Debug, Args)]
pub struct I2cRawWriteRead {
    /// Hex data bytes to write.
    #[arg(short = 'd', long)]
    hexdata: String,
    /// Number of bytes to read.
    #[arg(short = 'n', long, value_parser = usize::from_str)]
    length: usize,
}

#[derive(Debug, serde::Serialize)]
pub struct I2cRawWriteReadResponse {
    hexdata: String,
}

impl CommandDispatch for I2cRawWriteRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        let mut v = vec![0u8; self.length];
        i2c_bus.run_transaction(
            None,
            &mut [
                Transfer::Write(&hex::decode(&self.hexdata)?),
                Transfer::Read(&mut v),
            ],
        )?;
        Ok(Some(Box::new(I2cRawWriteReadResponse {
            hexdata: hex::encode(v),
        })))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum Mode {
    Host,
    Device,
}

#[derive(Debug, Args)]
pub struct I2cSetMode {
    pub mode: Mode,

    /// 7 bit I2C device address.
    #[arg(
        short,
        long,
        value_parser = u8::from_str
    )]
    pub addr: Option<u8>,
}

impl CommandDispatch for I2cSetMode {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        match self.mode {
            Mode::Host => i2c_bus.set_mode(i2c::Mode::Host)?,
            Mode::Device => match self.addr {
                Some(addr) => i2c_bus.set_mode(i2c::Mode::Device(addr))?,
                None => bail!("Must specify `--addr` after `set-mode device`"),
            },
        }
        Ok(None)
    }
}

/// Retrieve transcript of transfers since last time, and whether the I2C host is currently
/// waiting to READ data.
#[derive(Debug, Args)]
pub struct I2cGetDeviceStatus {
    /// For how long to wait, in case of nothing to report.
    #[arg(short,
    long,
    default_value="500ms",
    value_parser = humantime::parse_duration)]
    timeout: Duration,
}

#[derive(Debug, serde::Serialize)]
pub enum DeviceTransfer {
    /// The I2C host read a number of previously prepared bytes.
    Read {
        addr: u8,
        /// True if `I2cPrepareRead` was not called in time.
        timeout: bool,
        len: usize,
    },
    /// The I2C host wrote the given sequence of bytes.
    Write { addr: u8, hexdata: String },
}

#[derive(Debug, serde::Serialize)]
pub enum ReadStatus {
    /// Host has asked to read data, debugger device is currently stretching the clock waiting to
    /// be told what data to transmit via I2C.
    WaitingForData,
    /// Host is not asking to read data, and debugger also does not have any prepared data.
    Idle,
    /// Host is not asking to read data, debugger has prepared data for the case the host should
    /// ask in the future.
    DataPrepared,
}

#[derive(Debug, serde::Serialize)]
pub struct I2cGetDeviceStatusResponse {
    pub transfers: Vec<DeviceTransfer>,
    pub read_status: ReadStatus,
}

impl From<DeviceStatus> for I2cGetDeviceStatusResponse {
    fn from(ds: DeviceStatus) -> Self {
        let mut transfers = Vec::new();
        for t in ds.transfers {
            transfers.push(match t {
                i2c::DeviceTransfer::Read { addr, timeout, len } => {
                    DeviceTransfer::Read { addr, timeout, len }
                }
                i2c::DeviceTransfer::Write { addr, data } => DeviceTransfer::Write {
                    addr,
                    hexdata: hex::encode(data),
                },
            });
        }
        Self {
            transfers,
            read_status: match ds.read_status {
                i2c::ReadStatus::WaitingForData(_) => ReadStatus::WaitingForData,
                i2c::ReadStatus::Idle => ReadStatus::Idle,
                i2c::ReadStatus::DataPrepared => ReadStatus::DataPrepared,
            },
        }
    }
}

impl CommandDispatch for I2cGetDeviceStatus {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        let status = i2c_bus.get_device_status(self.timeout)?;
        let response = I2cGetDeviceStatusResponse::from(status);
        Ok(Some(Box::new(response)))
    }
}

/// Provide data that I2C device should send as part of READ transfer.
#[derive(Debug, Args)]
pub struct I2cPrepareRead {
    /// Hex data bytes as response to host reading.
    #[arg(short = 'd', long)]
    hexdata: String,

    /// Keep prepared response across WRITE transfers, if false prepared data will be discarded on
    /// any WRITE by I2C host, giving the caller a chance to review the additional data from the
    /// host, and revise the prepared responce.
    #[arg(short, long)]
    sticky: bool,
}

impl CommandDispatch for I2cPrepareRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::I2C).ok()?;
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let i2c_bus = context.params.create(transport, "DEFAULT")?;
        i2c_bus.prepare_read_data(&hex::decode(&self.hexdata)?, self.sticky)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct I2cTpm {
    #[command(subcommand)]
    command: super::tpm::TpmSubCommand,
}

impl CommandDispatch for I2cTpm {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let context = context.downcast_ref::<I2cCommand>().unwrap();
        let tpm_driver = tpm::I2cDriver::new(context.params.create(transport, "TPM")?);
        let bus: Box<dyn tpm::Driver> = Box::new(tpm_driver);
        self.command.run(&bus, transport)
    }
}

/// Commands for interacting with a generic I2C bus.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum InternalI2cCommand {
    RawRead(I2cRawRead),
    RawWrite(I2cRawWrite),
    RawWriteRead(I2cRawWriteRead),
    GetDeviceStatus(I2cGetDeviceStatus),
    PrepareRead(I2cPrepareRead),
    SetMode(I2cSetMode),
    Tpm(I2cTpm),
}

#[derive(Debug, Args)]
pub struct I2cCommand {
    #[command(flatten)]
    params: I2cParams,

    #[command(subcommand)]
    command: InternalI2cCommand,
}

impl CommandDispatch for I2cCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // None of the I2C commands care about the prior context, but they do
        // care about the `bus` parameter in the current node.
        self.command.run(self, transport)
    }
}
