// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::io::{ErrorKind, Read, Write};
use std::os::fd::{AsRawFd, BorrowedFd};
use std::time::Duration;

use anyhow::{Context, Result};
use serialport::{ClearBuffer, Parity, SerialPort, TTYPort};

//use crate::io::uart::{Uart, UartError};
use crate::io::uart::{FlowControl, Uart, UartError};
use crate::transport::TransportError;
use crate::util;

/// Implementation of the `Uart` trait on top of a serial device, such as `/dev/ttyUSB0`.
pub struct SerialPortUart {
    flow_control: Cell<FlowControl>,
    port: RefCell<TTYPort>,
    rxbuf: RefCell<VecDeque<u8>>,
    pseudo_baud: Cell<u32>,
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
        let port = TTYPort::open(&serialport::new(port_name, baud))
            .map_err(|e| UartError::OpenError(e.to_string()))?;
        flock_serial(&port, port_name)?;
        Ok(SerialPortUart {
            flow_control: Cell::new(FlowControl::None),
            port: RefCell::new(port),
            rxbuf: RefCell::default(),
            pseudo_baud: Cell::new(0),
        })
    }

    /// Open a pseudo port (e.g. a verilator pts device).
    pub fn open_pseudo(port_name: &str, baud: u32) -> Result<Self> {
        let port = TTYPort::open(&serialport::new(port_name, baud))
            .map_err(|e| UartError::OpenError(e.to_string()))?;
        flock_serial(&port, port_name)?;
        Ok(SerialPortUart {
            flow_control: Cell::new(FlowControl::None),
            port: RefCell::new(port),
            rxbuf: RefCell::default(),
            pseudo_baud: Cell::new(baud),
        })
    }

    fn read_worker(&self, timeout: Duration) -> Result<()> {
        let mut buf = [0u8; 256];
        let mut port = self.port.borrow_mut();

        port.set_timeout(timeout).context("UART read error")?;
        let result = port.read(&mut buf);
        let len = match result {
            Ok(n) => n,
            Err(ioerr) if ioerr.kind() == ErrorKind::TimedOut => 0,
            Err(e) => return Err(e.into()),
        };
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
        port.set_timeout(Self::FOREVER).context("UART read error")?;
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

impl Uart for SerialPortUart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        let pseudo = self.pseudo_baud.get();
        if pseudo == 0 {
            self.port.borrow().baud_rate().context("getting baudrate")
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
                .set_baud_rate(baudrate)
                .map_err(|_| UartError::InvalidSpeed(baudrate))?;
        } else {
            self.pseudo_baud.set(baudrate);
        }
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

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        if self.rxbuf.borrow().is_empty() {
            self.read_worker(timeout)?;
        }
        self.read_buffer(buf)
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        self.read_timeout(buf, Self::FOREVER)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        // The constant of 10 is approximately 10 uart bit times per byte.
        let pacing = Duration::from_nanos(10 * 1_000_000_000u64 / (self.get_baudrate()? as u64));
        log::debug!(
            "flow control: {:?}, pacing = {:?}",
            self.flow_control.get(),
            pacing
        );

        if self.flow_control.get() == FlowControl::None {
            // Perform blocking write of all bytes in `buf` even if the mio library has put the
            // file descriptor into non-blocking mode.
            let mut port = self.port.borrow_mut();
            let mut idx = 0;
            while idx < buf.len() {
                match port.write(&buf[idx..]) {
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
            return Ok(());
        }

        for b in buf.iter() {
            // If flow control is enabled, read data from the input stream and
            // process the flow control chars.
            loop {
                self.read_worker(Duration::ZERO)?;
                // If we're ok to send, then break out of the flow-control loop and send the data.
                if self.flow_control.get() == FlowControl::Resume {
                    break;
                }
            }
            self.port
                .borrow_mut()
                .write_all(std::slice::from_ref(b))
                .context("UART write error")?;
            // Sleep one uart character time after writing to the uart to pace characters into the
            // usb-serial device so that we don't fill any device-internal buffers.  The Chip Whisperer board (for
            // example) appears to have a large internal buffer that will keep transmitting to OT
            // even if an XOFF is sent.
            std::thread::sleep(pacing);
        }
        Ok(())
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        let port = self.port.borrow_mut();
        if enable {
            port.set_break()?;
        } else {
            port.clear_break()?;
        }
        Ok(())
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.port.borrow_mut().set_parity(parity)?;
        Ok(())
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        self.rxbuf.borrow_mut().clear();
        self.port.borrow_mut().clear(ClearBuffer::Input)?;
        Ok(())
    }

    fn supports_nonblocking_read(&self) -> Result<bool> {
        Ok(true)
    }

    fn register_nonblocking_read(&self, registry: &mio::Registry, token: mio::Token) -> Result<()> {
        let port: &mut TTYPort = &mut self.port.borrow_mut();
        registry.register(
            &mut mio::unix::SourceFd(&port.as_raw_fd()),
            token,
            mio::Interest::READABLE,
        )?;
        Ok(())
    }
}

/// Invoke Linux `flock()` on the given serial port, lock will be released when the file
/// descriptor is closed (or when the process terminates).
pub fn flock_serial(port: &TTYPort, port_name: &str) -> Result<()> {
    // SAFETY: `fd` is owned by `port` and is valid.
    let fd = unsafe { BorrowedFd::borrow_raw(port.as_raw_fd()) };
    rustix::fs::flock(fd, rustix::fs::FlockOperation::NonBlockingLockExclusive).map_err(|_| {
        TransportError::OpenError(port_name.to_string(), "Device is locked".to_string())
    })?;
    Ok(())
}
