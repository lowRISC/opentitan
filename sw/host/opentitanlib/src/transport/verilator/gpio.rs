// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Context, Result};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{self, ErrorKind, Read, Write};
use std::rc::Rc;
use std::time::Duration;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::verilator::transport::Inner;
use crate::transport::TransportError;
use crate::util::file;

pub struct VerilatorGpioPin {
    inner: Rc<RefCell<Inner>>,
    pinname: u8,
    out_value: Cell<bool>,
    pinmode: Cell<PinMode>,
    pullmode: Cell<PullMode>,
    default_level: bool,
}

impl VerilatorGpioPin {
    pub(crate) fn new(inner: Rc<RefCell<Inner>>, pinname: u8, default_level: bool) -> Rc<Self> {
        Rc::new(VerilatorGpioPin {
            inner,
            pinname,
            out_value: Cell::new(false),
            pinmode: Cell::new(PinMode::PushPull),
            pullmode: Cell::new(PullMode::None),
            default_level,
        })
    }

    fn set(&self) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.gpio.set(
            self.pinname,
            self.out_value.get(),
            self.pinmode.get(),
            self.pullmode.get(),
        )
    }
}

impl GpioPin for VerilatorGpioPin {
    fn read(&self) -> Result<bool> {
        let mut inner = self.inner.borrow_mut();
        inner.gpio.get(self.pinname)
    }

    fn write(&self, value: bool) -> Result<()> {
        self.out_value.set(value);
        self.set()
    }

    fn reset(&self) -> Result<()> {
        self.write(self.default_level)
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.pinmode.set(mode);
        self.set()
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.pullmode.set(mode);
        self.set()
    }

    /// Atomically sets mode, value, and weak pull.
    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> Result<()> {
        if analog_value.is_some() {
            return Err(TransportError::UnsupportedOperation.into());
        }
        if let Some(mode) = mode {
            self.pinmode.set(mode);
        }
        if let Some(pull) = pull {
            self.pullmode.set(pull);
        }
        if let Some(value) = value {
            self.out_value.set(value);
        }
        self.set()
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
                            b'0' => self.rval & !(1 << (31 - i)),
                            b'1' => self.rval | 1 << (31 - i),
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

    fn set(&mut self, index: u8, val: bool, mode: PinMode, weak_pull: PullMode) -> Result<()> {
        let code = match (mode, val, weak_pull) {
            (PinMode::PushPull, true, _) => "h",
            (PinMode::PushPull, false, _) => "l",
            (PinMode::OpenDrain, false, _) => "l",
            // If none of the above match, then there is no strong drive, inspect weak pull mode.
            (_, _, PullMode::PullUp) => "wh",
            (_, _, PullMode::PullDown) => "wl",
            (_, _, PullMode::None) => "wl", // High-Z not implemented in gpiodpi
        };
        let command = format!("{}{}\n", code, index);
        self.write
            .write(command.as_bytes())
            .context("GPIO write error")?;
        Ok(())
    }
}
