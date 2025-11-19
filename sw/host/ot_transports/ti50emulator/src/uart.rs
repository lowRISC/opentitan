// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{RefCell, RefMut};
use std::path::PathBuf;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, ready};

use anyhow::{Context as _, Result};
use tokio::io::{AsyncRead, AsyncWriteExt};
use tokio::net::UnixStream;

use opentitanlib::io::console::ConsoleDevice;
use opentitanlib::io::emu::EmuState;
use opentitanlib::io::uart::{Uart, UartError};
use opentitanlib::util::runtime::MultiWaker;

use super::Inner;

const TI50_UART_BAUDRATE: u32 = 115200;

pub struct Ti50Uart {
    inner: Rc<Inner>,
    // This socket is valid as long as SubProcess is running.
    socket: RefCell<Option<UnixStream>>,
    // full path to socket file
    path: PathBuf,
    multi_waker: MultiWaker,
}

impl Ti50Uart {
    pub fn open(inner: &Rc<Inner>, path: &str) -> Result<Self> {
        let soc_path = inner.process.borrow().get_runtime_dir().join(path);
        Ok(Self {
            inner: inner.clone(),
            socket: RefCell::default(),
            path: soc_path,
            multi_waker: MultiWaker::new(),
        })
    }

    // Called when a emulator sub-process starts up, after the sub-process has created its Unix
    // pipes, but before it executes any project code.
    pub fn connect(&self) -> Result<()> {
        let mut socket = self.socket.borrow_mut();
        *socket = Some(
            opentitanlib::util::runtime::block_on(UnixStream::connect(&self.path))
                .context("UART reconect error")?,
        );
        Ok(())
    }

    pub fn get_state(&self) -> Result<EmuState> {
        let process = &mut self.inner.process.borrow_mut();
        process.update_status()?;
        Ok(process.get_state())
    }

    pub fn get_socket(&self) -> Result<RefMut<'_, UnixStream>> {
        Ok(RefMut::map(self.socket.borrow_mut(), |socket| {
            socket.as_mut().unwrap()
        }))
    }
}

impl ConsoleDevice for Ti50Uart {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        match self.get_state()? {
            EmuState::On => {
                let mut socket = self.get_socket()?;
                let mut read_buf = tokio::io::ReadBuf::new(buf);
                ready!(
                    self.multi_waker
                        .poll_with(cx, |cx| Pin::new(&mut *socket).poll_read(cx, &mut read_buf))
                )?;
                Poll::Ready(Ok(read_buf.filled().len()))
            }
            EmuState::Off => Poll::Pending,
            state => Err(UartError::GenericError(format!(
                "Operation not supported in Emulator state: {}",
                state
            )))?,
        }
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        match self.get_state()? {
            EmuState::On => {
                let mut socket = self.get_socket()?;
                opentitanlib::util::runtime::block_on(socket.write(buf))
                    .context("UART read error")?;
                Ok(())
            }
            state => {
                log::warn!("Ignoring write when DUT is state: {}", state);
                Ok(())
            }
        }
    }
}

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
}
