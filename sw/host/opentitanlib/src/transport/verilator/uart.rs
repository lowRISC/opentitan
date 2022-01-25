// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::RefCell;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::time::Duration;

use crate::io::uart::Uart;
use crate::util::file;

/// Represents the verilator virtual UART.
pub struct VerilatorUart {
    file: RefCell<File>,
}

impl VerilatorUart {
    pub fn open(path: &str) -> Result<Self> {
        Ok(VerilatorUart {
            file: RefCell::new(OpenOptions::new().read(true).write(true).open(path)?),
        })
    }
}

impl Uart for VerilatorUart {
    fn get_baudrate(&self) -> u32 {
        // The verilator UART operates at 7200 baud.
        // See `sw/device/lib/arch/device_sim_verilator.c`.
        7200
    }

    fn set_baudrate(&self, _baudrate: u32) -> Result<()> {
        // As a virtual uart, setting the baudrate is a no-op.
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let mut file = self.file.borrow_mut();
        file::wait_read_timeout(&*file, timeout)?;
        Ok(file.read(buf)?)
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        Ok(self.file.borrow_mut().read(buf)?)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        Ok(self.file.borrow_mut().write_all(buf)?)
    }
}
