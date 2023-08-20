// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;
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
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(I2cError);

/// Represents a I2C transfer.
pub enum Transfer<'rd, 'wr> {
    Read(&'rd mut [u8]),
    Write(&'wr [u8]),
}

/// A trait which represents a I2C Bus.
pub trait Bus {
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
}
