// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};

use std::cell::{Cell, RefCell, RefMut};
use std::io::{ErrorKind, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Duration;

use crate::io::emu::EmuState;
use crate::io::uart::{Uart, UartError};
use crate::transport::ti50emulator::emu::EMULATOR_INVALID_ID;
use crate::transport::ti50emulator::Inner;
use crate::transport::ti50emulator::Ti50Emulator;

const TI50_UART_BAUDRATE: u32 = 115200;

pub struct Ti50Uart {
    inner: Rc<RefCell<Inner>>,
    // This socket is valid as long as SubProcess is running.
    socket: RefCell<Option<UnixStream>>,
    // full path to socket file
    path: PathBuf,
    // last SubProcess ID
    last_id: Cell<u64>,
}

impl Ti50Uart {
    pub fn open(ti50: &Ti50Emulator, path: &str) -> Result<Self> {
        let soc_path = ti50.inner.borrow().process.get_runtime_dir().join(path);
        Ok(Self {
            inner: Rc::clone(&ti50.inner),
            socket: RefCell::default(),
            path: soc_path,
            last_id: Cell::new(EMULATOR_INVALID_ID),
        })
    }

    pub fn reconnect(&self) -> Result<()> {
        let mut socket = self.socket.borrow_mut();
        let id = self.inner.borrow_mut().process.get_id();
        if self.last_id.get() != id {
            *socket = Some(UnixStream::connect(&self.path).context("UART reconect error")?);
            self.last_id.set(id);
        }
        Ok(())
    }

    pub fn get_state(&self) -> Result<EmuState> {
        let process = &mut self.inner.borrow_mut().process;
        process.update_status()?;
        Ok(process.get_state())
    }

    pub fn get_socket(&self) -> Result<RefMut<UnixStream>> {
        self.reconnect()?;
        return Ok(RefMut::map(self.socket.borrow_mut(), |socket| {
            socket.as_mut().unwrap()
        }));
    }
}

/// A trait which represents a UART.
impl Uart for Ti50Uart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        // As a virtual uart, the value is set only for compatibility with common hardware
        // Real speed of uart is much higher and it is mostly limited by IPC speed.
        Ok(TI50_UART_BAUDRATE)
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, _baudrate: u32) -> Result<()> {
        // As a virtual uart, setting the baudrate is a no-op.
        Ok(())
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        match self.get_state()? {
            EmuState::On => {
                let mut socket = self.get_socket()?;
                socket.set_read_timeout(None)?;
                Ok(socket.read(buf)?)
            }
            EmuState::Off => Ok(0),
            state => Err(UartError::GenericError(format!(
                "Operation not supported in Emulator state: {}",
                state
            ))
            .into()),
        }
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        match self.get_state()? {
            EmuState::On => {
                let mut socket = self.get_socket()?;
                socket
                    .set_read_timeout(Some(timeout))
                    .context("Set timeoout")?;
                match socket.read(buf) {
                    Ok(n) => Ok(n),
                    Err(error) => match error.kind() {
                        ErrorKind::TimedOut | ErrorKind::WouldBlock => Ok(0),
                        _ => Err(error).context("UART read error?"),
                    },
                }
            }
            EmuState::Off => Ok(0),
            state => Err(UartError::GenericError(format!(
                "Operation not supported in Emulator state: {}",
                state
            ))
            .into()),
        }
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        match self.get_state()? {
            EmuState::On => {
                self.get_socket()?.write(buf).context("UART read error")?;
                Ok(())
            }
            state => {
                log::warn!("Ignoring write when DUT is state: {}", state);
                Ok(())
            }
        }
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        // Iterators are lazy, consume using `count()`.
        Read::by_ref(&mut *self.get_socket()?)
            .bytes()
            .take_while(Result::is_ok)
            .count();
        Ok(())
    }
}
