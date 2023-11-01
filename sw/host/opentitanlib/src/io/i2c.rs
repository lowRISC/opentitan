// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::time::Duration;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;
use crate::transport::TransportError;
use crate::util::parse_int::ParseInt;

#[derive(Debug, Args)]
pub struct I2cParams {
    /// I2C instance.
    #[arg(long)]
    pub bus: Option<String>,

    /// I2C bus speed (typically: 100000, 400000, 1000000).
    #[arg(long)]
    pub speed: Option<u32>,

    /// 7 bit I2C device address.
    #[arg(
        short,
        long,
        value_parser = u8::from_str
    )]
    pub addr: Option<u8>,
}

impl I2cParams {
    pub fn create(
        &self,
        transport: &TransportWrapper,
        default_instance: &str,
    ) -> Result<Rc<dyn Bus>> {
        let i2c = transport.i2c(self.bus.as_deref().unwrap_or(default_instance))?;
        if let Some(speed) = self.speed {
            i2c.set_max_speed(speed)?;
        }
        if let Some(addr) = self.addr {
            i2c.set_default_address(addr)?;
        }
        Ok(i2c)
    }
}

/// Errors related to the I2C interface and I2C transactions.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum I2cError {
    #[error("Invalid data length: {0}")]
    InvalidDataLength(usize),
    #[error("Bus timeout")]
    Timeout,
    #[error("Bus busy")]
    Busy,
    #[error("Missing I2C address")]
    MissingAddress,
    #[error("I2C port not in device mode")]
    NotInDeviceMode,
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(I2cError);

/// Represents a I2C transfer to be initiated by the debugger as I2C host.
pub enum Transfer<'rd, 'wr> {
    Read(&'rd mut [u8]),
    Write(&'wr [u8]),
}

/// Status of I2C read operations (data from device to host).
#[derive(Debug, Deserialize, Serialize)]
pub enum ReadStatus {
    /// Host has asked to read data, debugger device is currently stretching the clock waiting to
    /// be told what data to transmit via I2C.  Parameter is 7-bit I2C address.
    WaitingForData(u8),
    /// Host is not asking to read data, and debugger also does not have any prepared data.
    Idle,
    /// Host is not asking to read data, debugger has prepared data for the case the host should
    /// ask in the future.
    DataPrepared,
}

/// Record of one transfer initiated by the I2C host, to which the debugger responded as I2C
/// device.
#[derive(Debug, Deserialize, Serialize)]
pub enum DeviceTransfer {
    /// The I2C host read a number of previously prepared bytes.
    Read {
        addr: u8,
        /// True if `prepare_read_data()` was not called in time.
        timeout: bool,
        len: usize,
    },
    /// The I2C host wrote the given sequence of bytes.
    Write { addr: u8, data: Vec<u8> },
}

/// A log of I2C operations performed by the I2C host since last time, as well as whether the I2C
/// host is currently waiting to read data.
#[derive(Debug, Deserialize, Serialize)]
pub struct DeviceStatus {
    /// Log of transfers completed since the last time.
    pub transfers: Vec<DeviceTransfer>,
    /// Indicates whether the I2C host is currently waiting to read data (clock stretched by
    /// debugger).  If that is the case, the `tranfers` field above is guaranteed to contain all
    /// write (and read) transfers performed before the currently blocked read transfer (unless
    /// they have been already retrieved by a previous call to `get_device_status()`).
    pub read_status: ReadStatus,
}

#[derive(Debug, Deserialize, Serialize)]
pub enum Mode {
    /// Put I2C debugger into host mode (this is the default).
    Host,
    /// Put I2C debugger into device mode, address in low 7 bits.
    Device(u8),
}

/// A trait which represents a I2C Bus.
pub trait Bus {
    fn set_mode(&self, mode: Mode) -> Result<()> {
        if let Mode::Host = mode {
            Ok(())
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }

    //
    // Methods for use in host mode.
    //

    /// Gets the maximum allowed speed of the I2C bus.
    fn get_max_speed(&self) -> Result<u32>;
    /// Sets the maximum allowed speed of the I2C bus, typical values are 100_000, 400_000 or
    /// 1_000_000.
    fn set_max_speed(&self, max_speed: u32) -> Result<()>;

    /// Sets the "default" device address, used in cases when not overriden by parameter to
    /// `run_transaction()`.
    fn set_default_address(&self, addr: u8) -> Result<()>;

    /// Runs a I2C transaction composed from the slice of [`Transfer`] objects.  If `addr` is
    /// `None`, then the last value given to `set_default_adress()` is used instead.
    fn run_transaction(&self, addr: Option<u8>, transaction: &mut [Transfer]) -> Result<()>;

    //
    // Methods for use in device mode.
    //

    /// Retrieve a log of I2C operations performed by the I2C host since last time, as well as
    /// whether the I2C host is currently waiting to read data.
    fn get_device_status(&self, _timeout: Duration) -> Result<DeviceStatus> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Prepare data to be tranmitted to I2C host on future or currently waiting I2C read
    /// transfer.  By default, the prepared data will be discarded if the I2C issues a write
    /// transfer on the bus (giving the caller a chance to react to the additional data before
    /// preparing another response).  If the `sticky` parameter is `true`, the prepared data will
    /// be kept across any number of intervening write transfers, and used for a future read
    /// transfer.
    fn prepare_read_data(&self, _data: &[u8], _sticky: bool) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
