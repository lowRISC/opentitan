// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use safe_ftdi as ftdi;
use std::io::{Error, ErrorKind};
use std::io::{Read, Write};
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::ultradebug::Ultradebug;

/// Represents the Ultradebug UART.
pub struct UltradebugUart {
    device: ftdi::Device,
    baudrate: u32,
}

impl UltradebugUart {
    pub fn open(ultradebug: &Ultradebug) -> Result<Self> {
        let device = ultradebug.from_interface(ftdi::Interface::C)?;
        device.set_bitmode(0, ftdi::BitMode::Reset)?;
        device.set_baudrate(115200)?;
        // Read and write timeouts:
        device.set_timeouts(5000, 5000);
        Ok(UltradebugUart {
            device,
            baudrate: 115200,
        })
    }
}

impl Uart for UltradebugUart {
    fn get_baudrate(&self) -> u32 {
        self.baudrate
    }

    fn set_baudrate(&mut self, baudrate: u32) -> Result<()> {
        self.device.set_baudrate(baudrate)?;
        self.baudrate = baudrate;
        Ok(())
    }

    fn read_timeout(&mut self, buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        // Note: my recollection is that there is no way to set a read timeout
        // for the UART.  If there are no characters ready, the FTDI device
        // simply returns a zero-length read.
        Ok(self.read(buf)?)
    }
}

impl Read for UltradebugUart {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let n = self
            .device
            .read_data(buf)
            .map_err(|e| Error::new(ErrorKind::Other, e))?;
        Ok(n as usize)
    }
}

impl Write for UltradebugUart {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut total = 0usize;
        while total < buf.len() {
            let n = self
                .device
                .write_data(&buf[total..])
                .map_err(|e| Error::new(ErrorKind::Other, e))?;
            total += n as usize;
        }
        Ok(total)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
