// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::cmp;
use std::thread;
use std::time::{Duration, Instant};

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
        let device = ultradebug
            .from_interface(ftdi::Interface::C)
            .context("FTDI error")?;
        device
            .set_bitmode(0, ftdi::BitMode::Reset)
            .context("FTDI error")?;
        device.set_baudrate(115200).context("FTDI error")?;
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
    fn get_baudrate(&self) -> Result<u32> {
        Ok(self.inner.borrow().baudrate)
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.device.set_baudrate(baudrate).context("FTDI error")?;
        inner.baudrate = baudrate;
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let now = Instant::now();
        let count = self.read(buf).context("UART read error")?;
        if count > 0 {
            return Ok(count);
        }
        let short_delay = cmp::min(timeout.mul_f32(0.1), Duration::from_millis(20));
        while now.elapsed() < timeout {
            thread::sleep(short_delay);
            let count = self.read(buf).context("UART read error")?;
            if count > 0 {
                return Ok(count);
            }
        }
        Ok(0)
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        let n = self
            .inner
            .borrow()
            .device
            .read_data(buf)
            .context("UART read error")?;
        Ok(n as usize)
    }

    fn write(&self, mut buf: &[u8]) -> Result<()> {
        let inner = self.inner.borrow();
        while !buf.is_empty() {
            let n = inner.device.write_data(buf).context("UART write error")?;
            buf = &buf[n as usize..];
        }
        Ok(())
    }

    // TODO(#13290): Ideally, we would like to call `purge_usb_rx_buffer()` to clear the UART RX
    // buffer but our `libftdi` is too old:
    // safe_ftdi::Device::purge_usb_rx_buffer: error: undefined reference to 'ftdi_tciflush'
}
