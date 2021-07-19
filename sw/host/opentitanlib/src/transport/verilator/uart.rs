// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::time::Duration;

use crate::io::uart::Uart;
use crate::util::file;

/// Represents the verilator virtual UART.
pub struct VerilatorUart {
    file: File,
}

impl VerilatorUart {
    pub fn open(path: &str) -> Result<Self> {
        Ok(VerilatorUart {
            file: OpenOptions::new().read(true).write(true).open(path)?,
        })
    }
}

impl Uart for VerilatorUart {
    fn get_baudrate(&self) -> u32 {
        // The verilator UART operates at 7200 baud.
        // See `sw/device/lib/arch/device_sim_verilator.c`.
        7200
    }

    fn set_baudrate(&mut self, _baudrate: u32) -> Result<()> {
        // As a virtual uart, setting the baudrate is a no-op.
        Ok(())
    }

    fn read_timeout(&mut self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        file::wait_read_timeout(&self.file, timeout)?;
        Ok(self.file.read(buf)?)
    }
}

impl Read for VerilatorUart {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.file.read(buf)
    }
}

impl Write for VerilatorUart {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.file.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.file.flush()
    }
}
