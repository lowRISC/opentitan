// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use serialport::ClearBuffer;
use serialport::SerialPort;
use std::cell::RefCell;
use std::io::ErrorKind;
use std::time::Duration;

use crate::io::uart::{Uart, UartError};

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
                serialport::new(port_name, 115200)
                    .open()
                    .map_err(|e| UartError::OpenError(e.to_string()))?,
            ),
        })
    }
}

impl Uart for SerialPortUart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        self.port.borrow().baud_rate().context("getting baudrate")
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.port
            .borrow_mut()
            .set_baud_rate(baudrate)
            .map_err(|_| UartError::InvalidSpeed(baudrate))?;
        Ok(())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        Ok(self
            .port
            .borrow_mut()
            .read(buf)
            .context("UART read error")?)
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let mut port = self.port.borrow_mut();
        port.set_timeout(timeout).context("UART read error")?;
        let result = port.read(buf);
        let len = match result {
            Err(ioerr) if ioerr.kind() == ErrorKind::TimedOut => Ok(0),
            _ => result,
        };
        port.set_timeout(Self::FOREVER).context("UART read error")?;
        Ok(len.context("UART read error")?)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, mut buf: &[u8]) -> Result<()> {
        while buf.len() > 0 {
            let written = self
                .port
                .borrow_mut()
                .write(buf)
                .context("UART write error")?;
            buf = &buf[written..];
        }
        Ok(())
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        Ok(self.port.borrow_mut().clear(ClearBuffer::Input)?)
    }
}
