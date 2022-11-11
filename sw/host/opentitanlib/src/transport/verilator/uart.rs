// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
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
    rxbuf: RefCell<VecDeque<u8>>,
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
            rxbuf: RefCell::default(),
        })
    }

    fn read_worker(&self, timeout: Duration) -> Result<()> {
        let mut buf = [0u8; 256];
        let mut file = self.file.borrow_mut();

        if timeout != Duration::MAX {
            let ready = file::wait_read_timeout(&*file, timeout);
            match ready {
                Ok(_) => {}
                Err(e) => {
                    // A timeout from the simulated UART is not an error.  Let all other errors propagate.
                    if let Some(ioerr) = e.downcast_ref::<io::Error>() {
                        if ioerr.kind() == ErrorKind::TimedOut {
                            return Ok(());
                        }
                    }
                    return Err(e).context("UART read error");
                }
            }
        }

        let len = file.read(&mut buf)?;
        for &ch in &buf[..len] {
            if self.flow_control.get() != FlowControl::None {
                if ch == FlowControl::Resume as u8 {
                    log::debug!("Got RESUME");
                    self.flow_control.set(FlowControl::Resume);
                    continue;
                } else if ch == FlowControl::Pause as u8 {
                    log::debug!("Got PAUSE");
                    self.flow_control.set(FlowControl::Pause);
                    continue;
                }
            }
            self.rxbuf.borrow_mut().push_back(ch);
        }
        Ok(())
    }

    fn read_buffer(&self, buf: &mut [u8]) -> Result<usize> {
        let mut rxbuf = self.rxbuf.borrow_mut();
        let mut i = 0;
        for byte in buf.iter_mut() {
            let Some(rx) = rxbuf.pop_front() else {
                break;
            };
            *byte = rx;
            i += 1;
        }
        Ok(i)
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
        if self.rxbuf.borrow().is_empty() {
            self.read_worker(timeout)?;
        }
        self.read_buffer(buf)
    }

    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        self.read_timeout(buf, Duration::MAX)
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        // The constant of 10 is approximately 10 uart bit times per byte.
        let pacing = Duration::from_nanos(10 * 1_000_000_000u64 / (self.baudrate.get() as u64));

        for b in buf.iter() {
            // If flow control is enabled, read data from the input stream and
            // process the flow control chars.
            while self.flow_control.get() != FlowControl::None {
                self.read_worker(pacing)?;
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
