// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::time::Duration;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::transport::Result;

#[derive(Debug, StructOpt)]
pub struct UartParams {
    #[structopt(long, help = "UART instance", default_value = "CONSOLE")]
    uart: String,

    #[structopt(long, help = "UART baudrate")]
    baudrate: Option<u32>,
}

impl UartParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Uart>> {
        let uart = transport.uart(&self.uart)?;
        if let Some(baudrate) = self.baudrate {
            uart.set_baudrate(baudrate)?;
        }
        Ok(uart)
    }
}

/// A trait which represents a UART.
pub trait Uart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> u32;

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()>;
}

/// Errors related to the UART interface.  These error messages will be printed in the context
/// of a TransportError::UartError, that is "UART error: {}".  So including the words "error" or
/// "serial" in texts below will probably be redundant.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum UartError {
    #[error("Enumerating: {0}")]
    EnumerationError(String),
    #[error("Opening: {0}")]
    OpenError(String),
    #[error("Invalid option: {0}")]
    InvalidOption(String),
    #[error("Invalid speed: {0}")]
    InvalidSpeed(u32),
    #[error("Reading: {0}")]
    ReadError(String),
    #[error("Writing: {0}")]
    WriteError(String),
}

