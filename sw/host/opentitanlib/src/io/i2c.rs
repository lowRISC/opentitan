// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;

#[derive(Debug, StructOpt)]
pub struct I2cParams {
    #[structopt(long, help = "I2C instance", default_value = "0")]
    pub bus: String,

    #[structopt(long, help = "I2C bus speed (typically: 100000, 400000, 1000000)")]
    pub speed: Option<u32>,
}

impl I2cParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Bus>> {
        let i2c = transport.i2c(&self.bus)?;
        if let Some(speed) = self.speed {
            i2c.set_max_speed(speed)?;
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

    /// Runs a I2C transaction composed from the slice of [`Transfer`] objects.
    fn run_transaction(&self, addr: u8, transaction: &mut [Transfer]) -> Result<()>;
}
