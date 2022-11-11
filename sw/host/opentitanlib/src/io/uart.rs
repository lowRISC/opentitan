// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::time::Duration;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;

#[derive(Clone, Debug, StructOpt, Serialize, Deserialize)]
pub struct UartParams {
    #[structopt(long, help = "UART instance", default_value = "CONSOLE")]
    uart: String,

    #[structopt(long, help = "UART baudrate")]
    baudrate: Option<u32>,

    #[structopt(long, help = "Enable software flow control")]
    flow_control: bool,
}

impl UartParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Uart>> {
        let uart = transport.uart(&self.uart)?;
        if let Some(baudrate) = self.baudrate {
            uart.set_baudrate(baudrate)?;
        }
        log::info!("set_flow_control to {}", self.flow_control);
        uart.set_flow_control(self.flow_control)?;
        Ok(uart)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum FlowControl {
    // No flow control.
    None = 0,
    // Pause aka XOFF aka Ctrl-S ("Stop")
    Pause = 19,
    // Resume aka XON aka Ctrl-Q ("Quit Stopping")
    Resume = 17,
}

/// A trait which represents a UART.
pub trait Uart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32>;

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()>;

    /// Enables software flow control for `write`s.
    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        if flow_control {
            unimplemented!();
        }
        Ok(())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()>;

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        // Keep reading while until the RX buffer is empty.
        // Note: This default implementation is overriden in backends where we can do better.
        const TIMEOUT: Duration = Duration::from_millis(5);
        let mut buf = [0u8; 256];
        while self.read_timeout(&mut buf, TIMEOUT)? > 0 {}
        Ok(())
    }
}

/// Errors related to the UART interface.
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
    #[error("{0}")]
    GenericError(String),
}
impl_serializable_error!(UartError);
