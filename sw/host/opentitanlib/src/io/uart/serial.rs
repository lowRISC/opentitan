// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::io::{ErrorKind, Read, Write};
use std::os::fd::{AsRawFd, BorrowedFd};
use std::task::{Context, Poll, ready};
use std::time::Duration;

use anyhow::{Context as _, Result};
use serialport::{ClearBuffer, SerialPort, TTYPort};
use tokio::io::unix::AsyncFd;

use super::{Parity, Uart, UartError};
use crate::io::console::{ConsoleDevice, ConsoleExt};
use crate::util;
use crate::util::runtime::MultiWaker;

/// Implementation of the `Uart` trait on top of a serial device, such as `/dev/ttyUSB0`.
pub struct SerialPortUart {
    port_name: String,
    port: RefCell<AsyncFd<TTYPort>>,
    pseudo_baud: Cell<u32>,
    multi_waker: MultiWaker,
}

impl SerialPortUart {
    // Not really forever, but close enough.  I'd rather use Duration::MAX, but
    // it seems that the serialport library can compute an invalid `timeval` struct
    // to pass to `poll`, which then leads to an `Invalid argument` error when
    // trying to `read` or `write` without a timeout.  One hundred years should be
    // longer than any invocation of this program.
    const FOREVER: Duration = Duration::from_secs(100 * 365 * 86400);

    /// Open the given serial device, such as `/dev/ttyUSB0`.
    pub fn open(port_name: &str, baud: u32) -> Result<Self> {
        let port = TTYPort::open(&serialport::new(port_name, baud).preserve_dtr_on_open())
            .map_err(|e| UartError::OpenError(e.to_string()))?;
        let _runtime_guard = crate::util::runtime().enter();
        let port = AsyncFd::new(port)?;
        flock_serial(port.get_ref(), port_name)?;
        Ok(SerialPortUart {
            port_name: port_name.to_string(),
            port: RefCell::new(port),
            pseudo_baud: Cell::new(0),
            multi_waker: MultiWaker::new(),
        })
    }

    /// Open a pseudo port (e.g. a verilator pts device).
    pub fn open_pseudo(port_name: &str, baud: u32) -> Result<Self> {
        let port = TTYPort::open(&serialport::new(port_name, baud).preserve_dtr_on_open())
            .map_err(|e| UartError::OpenError(e.to_string()))?;
        let _runtime_guard = crate::util::runtime().enter();
        let port = AsyncFd::new(port)?;
        flock_serial(port.get_ref(), port_name)?;
        Ok(SerialPortUart {
            port_name: port_name.to_string(),
            port: RefCell::new(port),
            pseudo_baud: Cell::new(baud),
            multi_waker: MultiWaker::new(),
        })
    }
}

impl ConsoleDevice for SerialPortUart {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        let mut port = self.port.borrow_mut();

        loop {
            let mut guard = ready!(
                self.multi_waker
                    .poll_with(cx, |cx| port.poll_read_ready_mut(cx))
            )?;

            match guard.try_io(|inner| {
                inner.get_mut().set_timeout(Duration::ZERO)?;
                let result = match inner.get_mut().read(buf) {
                    Ok(n) => Ok(n),
                    Err(ioerr) if ioerr.kind() == ErrorKind::TimedOut => {
                        Err(std::io::Error::new(std::io::ErrorKind::WouldBlock, ioerr))
                    }
                    Err(ioerr) => Err(ioerr)?,
                };
                inner.get_mut().set_timeout(Self::FOREVER)?;
                result
            }) {
                Ok(result) => return Poll::Ready(Ok(result?)),
                Err(_would_block) => continue,
            }
        }
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        // Perform blocking write of all bytes in `buf` even if the mio library has put the
        // file descriptor into non-blocking mode.
        let mut port = self.port.borrow_mut();
        let mut idx = 0;
        while idx < buf.len() {
            match port.get_mut().write(&buf[idx..]) {
                Ok(n) => idx += n,
                Err(ioerr) if ioerr.kind() == ErrorKind::TimedOut => {
                    // Buffers are full, file descriptor is non-blocking.  Explicitly wait for
                    // this one file descriptor to again become ready for writing.  Since this
                    // is a UART, we know that it will become ready in bounded time.
                    util::file::wait_timeout(
                        // SAFETY: The file descriptor is owned by `port` and is valid.
                        unsafe { BorrowedFd::borrow_raw(port.as_raw_fd()) },
                        rustix::event::PollFlags::OUT,
                        Duration::from_secs(5),
                    )?;
                }
                Err(ioerr) => return Err(ioerr).context("UART communication error"),
            }
        }

        Ok(())
    }
}

impl Uart for SerialPortUart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        let pseudo = self.pseudo_baud.get();
        if pseudo == 0 {
            self.port
                .borrow()
                .get_ref()
                .baud_rate()
                .context("getting baudrate")
        } else {
            Ok(pseudo)
        }
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        let pseudo = self.pseudo_baud.get();
        if pseudo == 0 {
            self.port
                .borrow_mut()
                .get_mut()
                .set_baud_rate(baudrate)
                .map_err(|_| UartError::InvalidSpeed(baudrate))?;
        } else {
            self.pseudo_baud.set(baudrate);
        }
        Ok(())
    }

    fn get_device_path(&self) -> Result<String> {
        Ok(self.port_name.clone())
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.port.borrow_mut().get_mut().set_parity(parity)?;
        Ok(())
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        self.port.borrow_mut().get_mut().clear(ClearBuffer::Input)?;

        // There might still be data in the device buffer, try to
        // drain that as well.
        //
        // NOTE This code will only have an effect on backends that
        // use SerialPortUart and do not override clear_rx_buffer,
        // such as the chip_whisperer backend (which uses the SAM3x
        // for UART). On backends such as hyperdebug which have a specific
        // mechanism to clear the device buffers, following code will not
        // doing anything useful.
        const TIMEOUT: Duration = Duration::from_millis(5);
        let mut buf = [0u8; 256];
        while self.read_timeout(&mut buf, TIMEOUT)? > 0 {}
        Ok(())
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        let mut port = self.port.borrow_mut();
        if enable {
            port.get_mut().set_break()?;
        } else {
            port.get_mut().clear_break()?;
        }
        Ok(())
    }

    fn borrow_fd(&self) -> Result<BorrowedFd<'_>> {
        let port = self.port.borrow();
        // SAFETY: `fd` is owned by `port` and is valid.
        let fd = unsafe { BorrowedFd::borrow_raw(port.as_raw_fd()) };
        Ok(fd)
    }
}

/// Invoke Linux `flock()` on the given serial port, lock will be released when the file
/// descriptor is closed (or when the process terminates).
pub fn flock_serial(port: &TTYPort, port_name: &str) -> Result<()> {
    // SAFETY: `fd` is owned by `port` and is valid.
    let fd = unsafe { BorrowedFd::borrow_raw(port.as_raw_fd()) };
    rustix::fs::flock(fd, rustix::fs::FlockOperation::NonBlockingLockExclusive)
        .map_err(|_| UartError::OpenError(format!("Device {port_name} is locked")))?;
    Ok(())
}
