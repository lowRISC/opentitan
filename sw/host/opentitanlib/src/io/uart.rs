// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::rc::Rc;
use std::time::Duration;
use structopt::StructOpt;

use crate::app::TransportWrapper;

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
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()>;
}
