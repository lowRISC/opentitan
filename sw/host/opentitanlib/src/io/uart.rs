// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::{self, Read};
use std::rc::Rc;
use std::task::{Context, Poll};
use std::time::Duration;

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
pub use serialport::Parity;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;
use crate::io::console::ConsoleDevice;
use crate::transport::TransportError;

#[derive(Clone, Debug, Args, Serialize, Deserialize)]
pub struct UartParams {
    /// UART instance.
    #[arg(long, default_value = "CONSOLE")]
    uart: String,

    /// UART baudrate.
    #[arg(long)]
    baudrate: Option<u32>,

    /// Enable software flow control.
    #[arg(long)]
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
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

    // Returns whether software flow control is enabled for the UART `write`s.
    fn get_flow_control(&self) -> Result<FlowControl> {
        unimplemented!();
    }

    /// Enables software flow control for `write`s.
    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        if flow_control {
            unimplemented!();
        }
        Ok(())
    }

    /// Returns `"/dev/ttyUSBn"` or similar OS device path usable by external programs for
    /// directly accessing the serial port.
    fn get_device_path(&self) -> Result<String> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function is blocking.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        crate::util::runtime::block_on(std::future::poll_fn(|cx| self.poll_read(cx, buf)))
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        crate::util::runtime::block_on(async {
            tokio::time::timeout(timeout, std::future::poll_fn(|cx| self.poll_read(cx, buf))).await
        })
        .unwrap_or(Ok(0))
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    ///
    /// If data is not yet ready, `Poll::Pending` will be returned and `cx` would be notified when it's available.
    /// When this function is called with multiple wakers, all wakers should be notified instead of just the last one.
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>>;

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

    fn set_break(&self, _enable: bool) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_parity(&self, _parity: Parity) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn get_parity(&self) -> Result<Parity> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

impl Read for &dyn Uart {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        Uart::read(&**self, buf).map_err(io::Error::other)
    }
}

impl<'a> ConsoleDevice for dyn Uart + 'a {
    fn console_poll_read(
        &self,
        cx: &mut std::task::Context<'_>,
        buf: &mut [u8],
    ) -> std::task::Poll<Result<usize>> {
        self.poll_read(cx, buf)
    }

    fn console_write(&self, buf: &[u8]) -> Result<()> {
        self.write(buf)
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        <Self as Uart>::set_break(self, enable)
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
