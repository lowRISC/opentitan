// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use serialport::ClearBuffer;
//use serialport::{FlowControl, SerialPort};
use serialport::SerialPort;
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::io::ErrorKind;
use std::time::Duration;

//use crate::io::uart::{Uart, UartError};
use crate::io::uart::{FlowControl, Uart, UartError};

/// Implementation of the `Uart` trait on top of a serial device, such as `/dev/ttyUSB0`.
pub struct SerialPortUart {
    flow_control: Cell<FlowControl>,
    port: RefCell<Box<dyn SerialPort>>,
    rxbuf: RefCell<VecDeque<u8>>,
}

impl SerialPortUart {
    // Not really forever, but close enough.  I'd rather use Duration::MAX, but
    // it seems that the serialport library can compute an invalid `timeval` struct
    // to pass to `poll`, which then leads to an `Invalid argument` error when
    // trying to `read` or `write` without a timeout.  One hundred years should be
    // longer than any invocation of this program.
    const FOREVER: Duration = Duration::from_secs(100 * 365 * 86400);

    /// Open the given serial device, such as `/dev/ttyUSB0`.
    pub fn open(port_name: &str) -> Result<Self> {
        Ok(SerialPortUart {
            flow_control: Cell::new(FlowControl::None),
            port: RefCell::new(
                serialport::new(port_name, 115200)
                    .open()
                    .map_err(|e| UartError::OpenError(e.to_string()))?,
            ),
            rxbuf: RefCell::default(),
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
        self.port.borrow().baud_rate().context("getting baudrate")
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.port
            .borrow_mut()
            .set_baud_rate(baudrate)
            .map_err(|_| UartError::InvalidSpeed(baudrate))?;
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
        log::debug!("pacing = {:?}", pacing);

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
            self.port
                .borrow_mut()
                .write_all(std::slice::from_ref(b))
                .context("UART write error")?;
        }
        Ok(())
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        self.rxbuf.borrow_mut().clear();
        self.port.borrow_mut().clear(ClearBuffer::Input)?;
        Ok(())
    }
}
