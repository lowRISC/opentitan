// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serialport::SerialPort;
use std::cell::RefCell;
use std::time::Duration;

use crate::io::uart::{Uart, UartError};
use crate::transport::{Result, WrapInTransportError};

/// Implementation of the `Uart` trait on top of a serial device, such as `/dev/ttyUSB0`.
pub struct SerialPortUart {
    port: RefCell<Box<dyn SerialPort>>,
}

impl SerialPortUart {
    // Not really forever, but close enough.  I'd rather use Duration::MAX, but
    // it seems that the serialport library can compute an invalid `timeval` struct
    // to pass to `poll`, which then leads to an `Invalid argument` error when
    // trying to `read` or `write` without a timeout.  One hundred years should be
    // longer than any invocation of this program.
    const FOREVER: Duration = Duration::from_secs(100 * 365 * 86400);

    /// Open the given serial device, such as `/dev/ttyUSB0`.
    pub fn open(port_name: &str) -> Result<Self> {
        Ok(SerialPortUart {
            port: RefCell::new(
                serialport::new(port_name, 115200).open().wrap(UartError::OpenError)?,
            ),
        })
    }
}

impl Uart for SerialPortUart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> u32 {
        self.port.borrow().baud_rate().unwrap()
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.port
            .borrow_mut()
            .set_baud_rate(baudrate)
            .wrap(|_| UartError::InvalidSpeed(baudrate))?;
        Ok(())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        Ok(self.port.borrow_mut().read(buf).wrap(UartError::ReadError)?)
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let mut port = self.port.borrow_mut();
        port.set_timeout(timeout).wrap(UartError::ReadError)?;
        let len = port.read(buf);
        port.set_timeout(Self::FOREVER).wrap(UartError::ReadError)?;
        Ok(len.wrap(UartError::ReadError)?)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, mut buf: &[u8]) -> Result<()> {
        while buf.len() > 0 {
            let written = self.port.borrow_mut().write(buf).wrap(UartError::WriteError)?;
            buf = &buf[written..];
        }
        Ok(())
    }
}
