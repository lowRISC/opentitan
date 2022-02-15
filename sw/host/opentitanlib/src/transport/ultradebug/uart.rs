// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::cmp;
use std::thread;
use std::time::{Duration, Instant};

use crate::io::uart::{Uart, UartError};
use crate::transport::ultradebug::Ultradebug;
use crate::transport::{Result, TransportError, WrapInTransportError};

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
        let device = ultradebug.from_interface(ftdi::Interface::C).wrap(TransportError::FtdiError)?;
        device.set_bitmode(0, ftdi::BitMode::Reset).wrap(TransportError::FtdiError)?;
        device.set_baudrate(115200).wrap(TransportError::FtdiError)?;
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
        inner.device.set_baudrate(baudrate).wrap(TransportError::FtdiError)?;
        inner.baudrate = baudrate;
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let now = Instant::now();
        let count = self.read(buf).wrap(UartError::ReadError)?;
        if count > 0 {
            return Ok(count);
        }
        let short_delay = cmp::min(timeout.mul_f32(0.1), Duration::from_millis(20));
        while now.elapsed() < timeout {
            thread::sleep(short_delay);
            let count = self.read(buf).wrap(UartError::ReadError)?;
            if count > 0 {
                return Ok(count);
            }
        }
        Ok(0)
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        let n = self.inner.borrow().device.read_data(buf).wrap(UartError::ReadError)?;
        Ok(n as usize)
    }

    fn write(&self, mut buf: &[u8]) -> Result<()> {
        let inner = self.inner.borrow();
        while buf.len() > 0 {
            let n = inner.device.write_data(buf).wrap(UartError::WriteError)?;
            buf = &buf[n as usize..];
        }
        Ok(())
    }
}
