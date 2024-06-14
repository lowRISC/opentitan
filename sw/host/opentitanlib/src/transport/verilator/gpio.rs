// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{self, ErrorKind, Read, Write};
use std::net::TcpStream;
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
}

impl VerilatorGpioPin {
    pub(crate) fn new(inner: Rc<RefCell<Inner>>, pinname: u8) -> Rc<Self> {
        Rc::new(VerilatorGpioPin {
            inner,
            pinname,
            out_value: Cell::new(false),
            pinmode: Cell::new(PinMode::PushPull),
            pullmode: Cell::new(PullMode::None),
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
    use_stream: bool,
    stream: Option<TcpStream>,
    read: Option<File>,
    write: Option<File>,
    rval: u32,
    pub pins: HashMap<u8, Rc<dyn GpioPin>>,
}

impl GpioInner {
    pub fn new(read_name: &str, write_name: &str) -> Result<Self> {
        let read;
        let write;
        let stream;
        let use_stream;

        // check if read_name is in TCP socket or pipe device format
        if read_name.contains(':') && !read_name.contains('/') {
            read = None;
            write = None;
            stream = Some(TcpStream::connect(read_name).map_err(|e| {
                TransportError::ProxyConnectError(read_name.to_string(), e.to_string())
            })?);
            use_stream = true;
        } else {
            read =
                Some(OpenOptions::new().read(true).open(read_name).map_err(|e| {
                    TransportError::OpenError(read_name.to_string(), e.to_string())
                })?);
            write = Some(
                OpenOptions::new()
                    .write(true)
                    .open(write_name)
                    .map_err(|e| {
                        TransportError::OpenError(write_name.to_string(), e.to_string())
                    })?,
            );
            stream = None;
            use_stream = false;
        }

        Ok(GpioInner {
            use_stream,
            stream,
            read,
            write,
            rval: 0,
            pins: HashMap::default(),
        })
    }

    fn read_stream(&mut self) -> Result<()> {
        if let Some(ref mut stream) = self.stream {
            let timeout = Duration::ZERO;

            if timeout != Duration::MAX {
                let result = stream.set_nonblocking(true);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("GPIO read error");
                    }
                }
                let result = stream.set_read_timeout(Some(timeout));
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("GPIO read error");
                    }
                }
            } else {
                let result = stream.set_nonblocking(false);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("GPIO read error");
                    }
                }
                let result = stream.set_read_timeout(None);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("GPIO read error");
                    }
                }
            }

            loop {
                let mut buf = [0u8; 33];
                match stream.read(&mut buf) {
                    Ok(n) => {
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
                        // A timeout from the simulated GPIO is not an error.  Let all other errors propagate.
                        if e.kind() == ErrorKind::WouldBlock {
                            return Ok(());
                        }
                        return Err(e).context("GPIO read error");
                    }
                }
            }
        } else {
            Err(anyhow!("TCP socket not connected")).context("GPIO read error")
        }
    }

    fn read_pipe(&mut self) -> Result<()> {
        if let Some(ref mut read) = self.read {
            loop {
                match file::wait_read_timeout(read, Duration::ZERO) {
                    Ok(()) => {
                        let mut buf = [0u8; 33];
                        let n = read.read(&mut buf).context("GPIO read error")?;
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
        } else {
            return Err(anyhow!("Read pipe not opened")).context("GPIO read error");
        }
        Ok(())
    }

    fn get(&mut self, index: u8) -> Result<bool> {
        if self.use_stream {
            self.read_stream()?;
        } else {
            self.read_pipe()?;
        }
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
        if self.use_stream {
            if let Some(ref mut stream) = self.stream {
                stream
                    .write(command.as_bytes())
                    .context("GPIO write error")?;
            } else {
                return Err(anyhow!("TCP socket not connected")).context("GPIO write error");
            }
        } else if let Some(ref mut write) = self.write {
            write
                .write(command.as_bytes())
                .context("GPIO write error")?;
        } else {
            return Err(anyhow!("Write pipe not opened")).context("GPIO write error");
        }
        Ok(())
    }
}
