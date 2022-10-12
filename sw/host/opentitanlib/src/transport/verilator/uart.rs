// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use std::cell::{Cell, RefCell};
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::{ErrorKind, Read, Write};
use std::io::{Seek, SeekFrom};
use std::time::Duration;

use crate::io::uart::{FlowControl, Uart};
use crate::transport::TransportError;
use crate::util::file;

/// Represents the verilator virtual UART.
pub struct VerilatorUart {
    baudrate: Cell<u32>,
    flow_control: Cell<FlowControl>,
    file: RefCell<File>,
}

impl VerilatorUart {
    pub fn open(path: &str) -> Result<Self> {
        Ok(VerilatorUart {
            // The verilator UART operates at 7200 baud.
            // See `sw/device/lib/arch/device_sim_verilator.c`.
            // The reality of the simulation is that the CPU can
            // only deal with about 4 chars per second.
            baudrate: Cell::new(40),
            flow_control: Cell::new(FlowControl::None),
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
        Ok(self.baudrate.get())
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        // As a virtual uart, setting the baudrate is a no-op.
        self.baudrate.set(baudrate);
        Ok(())
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.flow_control.set(match flow_control {
            false => FlowControl::None,
            // When flow-control is enabled, assume we're haven't
            // already been put into a pause state.
            true => FlowControl::Resume,
        });
        Ok(())
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        let ready = file::wait_read_timeout(&*self.file.borrow(), timeout);
        match ready {
            Ok(()) => self.read(buf),
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
        let mut n = self
            .file
            .borrow_mut()
            .read(buf)
            .context("UART read error")?;
        if self.flow_control.get() != FlowControl::None {
            // Eliminate flow control characters from the buffer
            let mut i = 0;
            while i < n {
                if buf[i] == FlowControl::Resume as u8 {
                    self.flow_control.set(FlowControl::Resume);
                    buf.copy_within((i + 1)..n, i);
                    n -= 1;
                } else if buf[i] == FlowControl::Pause as u8 {
                    self.flow_control.set(FlowControl::Pause);
                    buf.copy_within((i + 1)..n, i);
                    n -= 1;
                } else {
                    i += 1;
                }
            }
        }
        Ok(n)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        // The constant of 10 is approximately 10 uart bit times per byte.
        let pacing = Duration::from_nanos(10 * 1_000_000_000u64 / (self.baudrate.get() as u64));

        for b in buf.iter() {
            // If flow control is enabled, read and discard data from the input stream,
            // which will process the flow control chars.
            while self.flow_control.get() != FlowControl::None {
                let mut byte = 0;
                self.read_timeout(std::slice::from_mut(&mut byte), pacing)?;
                // If we're ok to send, then break out of the flow-control loop and send the data.
                if self.flow_control.get() == FlowControl::Resume {
                    break;
                }
            }
            self.file
                .borrow_mut()
                .write_all(std::slice::from_ref(b))
                .context("UART write error")?;
        }
        Ok(())
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        self.file.borrow_mut().seek(SeekFrom::End(0))?;
        Ok(())
    }
}
