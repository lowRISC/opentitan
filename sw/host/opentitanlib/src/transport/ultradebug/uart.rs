// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::ultradebug::Ultradebug;

pub struct Inner {
    device: ftdi::Device,
    baudrate: u32,
}

/// Represents the Ultradebug UART.
pub struct UltradebugUart {
    inner: RefCell<Inner>,
}

impl UltradebugUart {
    pub fn open(ultradebug: &Ultradebug) -> Result<Self> {
        let device = ultradebug.from_interface(ftdi::Interface::C)?;
        device.set_bitmode(0, ftdi::BitMode::Reset)?;
        device.set_baudrate(115200)?;
        // Read and write timeouts:
        device.set_timeouts(5000, 5000);
        Ok(UltradebugUart {
            inner: RefCell::new(Inner {
                device,
                baudrate: 115200,
            }),
        })
    }
}

impl Uart for UltradebugUart {
    fn get_baudrate(&self) -> u32 {
        self.inner.borrow().baudrate
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.device.set_baudrate(baudrate)?;
        inner.baudrate = baudrate;
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        // Note: my recollection is that there is no way to set a read timeout
        // for the UART.  If there are no characters ready, the FTDI device
        // simply returns a zero-length read.
        Ok(self.read(buf)?)
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        let n = self.inner.borrow().device.read_data(buf)?;
        Ok(n as usize)
    }

    fn write(&self, buf: &[u8]) -> Result<usize> {
        let mut total = 0usize;
        let inner = self.inner.borrow();
        while total < buf.len() {
            let n = inner.device.write_data(&buf[total..])?;
            total += n as usize;
        }
        Ok(total)
    }
}
