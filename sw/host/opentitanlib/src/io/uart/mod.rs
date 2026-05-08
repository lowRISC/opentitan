// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::{self, Read};
use std::os::fd::BorrowedFd;
use std::rc::Rc;
use std::time::Duration;

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
pub use serialport::Parity;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::impl_serializable_error;
use crate::io::console::{ConsoleDevice, ConsoleExt};
use crate::transport::TransportError;

pub mod flow;
pub mod serial;

#[derive(Clone, Debug, Default, Args, Serialize, Deserialize)]
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
pub trait Uart: ConsoleDevice {
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

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        // Keep reading while until the RX buffer is empty.
        // Note: This default implementation is overriden in backends where we can do better.
        const TIMEOUT: Duration = Duration::from_millis(5);
        let mut buf = [0u8; 256];
        while self.read_timeout(&mut buf, TIMEOUT)? > 0 {}
        Ok(())
    }

    fn set_parity(&self, _parity: Parity) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn get_parity(&self) -> Result<Parity> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn set_break(&self, _enable: bool) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn borrow_fd(&self) -> Result<BorrowedFd<'_>> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

impl<T: Uart + ?Sized> Uart for &T {
    fn get_baudrate(&self) -> Result<u32> {
        T::get_baudrate(self)
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        T::set_baudrate(self, baudrate)
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        T::get_flow_control(self)
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        T::set_flow_control(self, flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        T::get_device_path(self)
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        T::clear_rx_buffer(self)
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        T::set_parity(self, parity)
    }

    fn get_parity(&self) -> Result<Parity> {
        T::get_parity(self)
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        T::set_break(self, enable)
    }
}

impl<T: Uart + ?Sized> Uart for Rc<T> {
    fn get_baudrate(&self) -> Result<u32> {
        T::get_baudrate(self)
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        T::set_baudrate(self, baudrate)
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        T::get_flow_control(self)
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        T::set_flow_control(self, flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        T::get_device_path(self)
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        T::clear_rx_buffer(self)
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        T::set_parity(self, parity)
    }

    fn get_parity(&self) -> Result<Parity> {
        T::get_parity(self)
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        T::set_break(self, enable)
    }

    fn borrow_fd(&self) -> Result<BorrowedFd<'_>> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

impl Read for &dyn Uart {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        ConsoleExt::read(&**self, buf).map_err(io::Error::other)
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
