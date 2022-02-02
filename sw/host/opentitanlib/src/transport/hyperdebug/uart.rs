// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use std::cell::RefCell;
use std::io::Read;
use std::io::Write;
use std::path::Path;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::hyperdebug::Error;

pub struct HyperdebugUart {
    port: RefCell<Box<dyn serialport::SerialPort>>,
}

impl HyperdebugUart {
    pub fn open(tty: &Path) -> Result<Self> {
        let port = serialport::new(tty.to_str().ok_or(Error::UnicodePathError)?, 115_200)
            .timeout(Duration::from_millis(100))
            .open()
            .expect("Failed to open port");
        Ok(HyperdebugUart {
            port: RefCell::new(port),
        })
    }

    // Not really forever, but close enough.  I'd rather use Duration::MAX, but
    // it seems that the serialport library can compute an invalid `timeval` struct
    // to pass to `poll`, which then leads to an `Invalid argument` error when
    // trying to `read` or `write` without a timeout.  One hundred years should be
    // longer than any invocation of this program.
    const FOREVER: Duration = Duration::from_secs(100 * 365 * 86400);
}

impl Uart for HyperdebugUart {
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        self.port.borrow_mut().set_timeout(Self::FOREVER)?;
        Ok(self.port.borrow_mut().read(buf)?)
    }

    fn write(&self, mut buf: &[u8]) -> Result<()> {
        while buf.len() > 0 {
            let written = self.port.borrow_mut().write(buf)?;
            buf = &buf[written..];
        }
        Ok(())
    }

    fn get_baudrate(&self) -> u32 {
        match self.port.borrow().baud_rate() {
            Ok(baud_rate) => baud_rate,
            _ => panic!("SerialPort::baud_rate() returned Err"),
        }
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        Ok(self.port.borrow_mut().set_baud_rate(baudrate)?)
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        self.port.borrow_mut().set_timeout(timeout)?;
        Ok(self.port.borrow_mut().read(buf)?)
    }
}
