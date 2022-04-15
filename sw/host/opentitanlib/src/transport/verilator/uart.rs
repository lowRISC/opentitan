// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use std::cell::RefCell;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::{ErrorKind, Read, Write};
use std::time::Duration;

use crate::io::uart::Uart;
use crate::transport::TransportError;
use crate::util::file;

/// Represents the verilator virtual UART.
pub struct VerilatorUart {
    file: RefCell<File>,
}

impl VerilatorUart {
    pub fn open(path: &str) -> Result<Self> {
        Ok(VerilatorUart {
            file: RefCell::new(
                OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(path)
                    .map_err(|e| TransportError::OpenError(path.to_string(), e.to_string()))?,
            ),
        })
    }
}

impl Uart for VerilatorUart {
    fn get_baudrate(&self) -> Result<u32> {
        // The verilator UART operates at 7200 baud.
        // See `sw/device/lib/arch/device_sim_verilator.c`.
        Ok(7200)
    }

    fn set_baudrate(&self, _baudrate: u32) -> Result<()> {
        // As a virtual uart, setting the baudrate is a no-op.
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let mut file = self.file.borrow_mut();
        match file::wait_read_timeout(&*file, timeout) {
            Ok(()) => Ok(file.read(buf).context("UART read error")?),
            Err(e) => {
                // If we got a timeout from the uart, return 0 as per convention.
                // Let all other errors propagate.
                if let Some(ioerr) = e.downcast_ref::<io::Error>() {
                    if ioerr.kind() == ErrorKind::TimedOut {
                        return Ok(0);
                    }
                }
                Err(e).context("UART read error")
            }
        }
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        Ok(self
            .file
            .borrow_mut()
            .read(buf)
            .context("UART read error")?)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        Ok(self
            .file
            .borrow_mut()
            .write_all(buf)
            .context("UART write error")?)
    }
}
