// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Context, Result};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{self, ErrorKind, Read, Write};
use std::rc::Rc;
use std::time::Duration;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::verilator::transport::Inner;
use crate::util::file;

pub struct VerilatorGpioPin {
    inner: Rc<RefCell<Inner>>,
    pinname: u8,
}

impl VerilatorGpioPin {
    pub(crate) fn new(inner: Rc<RefCell<Inner>>, pinname: u8) -> Rc<Self> {
        Rc::new(VerilatorGpioPin { inner, pinname })
    }
}

impl GpioPin for VerilatorGpioPin {
    fn read(&self) -> Result<bool> {
        let mut inner = self.inner.borrow_mut();
        inner.gpio.get(self.pinname)
    }

    fn write(&self, value: bool) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.gpio.set(self.pinname, value)
    }

    fn set_mode(&self, _mode: PinMode) -> Result<()> {
        log::warn!("set_mode not implemented");
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        log::warn!("set_pull_mode not implemented");
        Ok(())
    }
}

pub(crate) struct GpioInner {
    read: File,
    write: File,
    rval: u32,
    pub pins: HashMap<u8, Rc<dyn GpioPin>>,
}

impl GpioInner {
    pub fn new(read: &str, write: &str) -> Result<Self> {
        let read = OpenOptions::new().read(true).open(read)?;
        let write = OpenOptions::new().write(true).open(write)?;
        Ok(GpioInner {
            read,
            write,
            rval: 0,
            pins: HashMap::default(),
        })
    }

    fn read_pipe(&mut self) -> Result<()> {
        loop {
            match file::wait_read_timeout(&self.read, Duration::ZERO) {
                Ok(()) => {
                    let mut buf = [0u8; 33];
                    let n = self.read.read(&mut buf).context("GPIO read error")?;
                    ensure!(
                        n == buf.len(),
                        GpioError::Generic(format!(
                            "Invalid gpio read length from simulator: {}",
                            n
                        ))
                    );
                    for (i, val) in buf.iter().enumerate() {
                        self.rval = match val {
                            b'0' => self.rval & !(1 << 31 - i),
                            b'1' => self.rval | 1 << 31 - i,
                            b'\n' | b'X' => self.rval,
                            _ => {
                                return Err(GpioError::Generic(format!(
                                    "Invalid gpio status from simulator: {:?}",
                                    std::str::from_utf8(&buf)
                                ))
                                .into());
                            }
                        };
                    }
                }
                Err(e) => {
                    if let Some(ioerr) = e.downcast_ref::<io::Error>() {
                        if ioerr.kind() == ErrorKind::TimedOut {
                            break;
                        }
                    }
                    return Err(e).context("GPIO read error");
                }
            }
        }
        Ok(())
    }

    fn get(&mut self, index: u8) -> Result<bool> {
        self.read_pipe()?;
        Ok(self.rval & (1 << index) != 0)
    }

    fn set(&mut self, index: u8, val: bool) -> Result<()> {
        let command = if val {
            format!("h{}\n", index)
        } else {
            format!("l{}\n", index)
        };
        self.write
            .write(command.as_bytes())
            .context("GPIO write error")?;
        Ok(())
    }
}
