// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Context, Result};
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::{ErrorKind, Read, Write};
//use std::io::{Seek, SeekFrom};
use std::net::TcpStream;
use std::time::Duration;

use crate::io::uart::{FlowControl, Uart};
use crate::transport::TransportError;
use crate::util::file;

/// Represents the verilator virtual UART.
pub struct VerilatorUart {
    baudrate: Cell<u32>,
    flow_control: Cell<FlowControl>,
    use_stream: bool,
    stream: Option<RefCell<TcpStream>>,
    pipe: Option<RefCell<File>>,
    rxbuf: RefCell<VecDeque<u8>>,
}

impl VerilatorUart {
    pub fn open(name: &str) -> Result<Self> {
        let ref_pipe;
        let ref_stream;
        let use_stream;

        // check if read_name is in TCP socket or pipe device format
        if name.contains(':') && !name.contains('/') {
            let stream = TcpStream::connect(name)
                .map_err(|e| TransportError::ProxyConnectError(name.to_string(), e.to_string()))?;

            ref_pipe = None;
            ref_stream = Some(RefCell::new(stream));
            use_stream = true;
        } else {
            let pipe = OpenOptions::new()
                .read(true)
                .write(true)
                .open(name)
                .map_err(|e| TransportError::OpenError(name.to_string(), e.to_string()))?;

            ref_pipe = Some(RefCell::new(pipe));
            ref_stream = None;
            use_stream = false;
        }

        Ok(VerilatorUart {
            // The verilator UART operates at 7200 baud.
            // See `sw/top_<chip>/sw/device/arch/device_sim_verilator.c`.
            // The reality of the simulation is that the CPU can
            // only deal with about 4 chars per second.
            baudrate: Cell::new(40),
            flow_control: Cell::new(FlowControl::None),
            use_stream,
            stream: ref_stream,
            pipe: ref_pipe,
            rxbuf: RefCell::default(),
        })
    }

    fn read_stream(&self, timeout: Duration) -> Result<()> {
        if let Some(ref ref_stream) = self.stream {
            let mut buf = [0u8; 256];
            let mut stream = ref_stream.borrow_mut();

            if timeout != Duration::MAX {
                let result = stream.set_nonblocking(true);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("UART read error");
                    }
                }
                let result = stream.set_read_timeout(Some(timeout));
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("UART read error");
                    }
                }
            } else {
                let result = stream.set_nonblocking(false);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("UART read error");
                    }
                }
                let result = stream.set_read_timeout(None);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("UART read error");
                    }
                }
            }

            match stream.read(&mut buf) {
                Ok(len) => {
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
                }
                Err(e) => {
                    // A timeout from the simulated UART is not an error.
                    // Let all other errors propagate.
                    if e.kind() == ErrorKind::WouldBlock {
                        return Ok(());
                    }
                    return Err(e).context("UART read error");
                }
            }
        } else {
            return Err(anyhow!("TCP socket not connected")).context("UART read error");
        }
        Ok(())
    }

    fn read_pipe(&self, timeout: Duration) -> Result<()> {
        if let Some(ref ref_pipe) = self.pipe {
            let mut buf = [0u8; 256];
            let mut pipe = ref_pipe.borrow_mut();

            if timeout != Duration::MAX {
                let ready = file::wait_read_timeout(&*pipe, timeout);
                match ready {
                    Ok(_) => {}
                    Err(e) => {
                        // A timeout from the simulated UART is not an error.
                        // Let all other errors propagate.
                        if let Some(ioerr) = e.downcast_ref::<io::Error>() {
                            if ioerr.kind() == ErrorKind::TimedOut {
                                return Ok(());
                            }
                        }
                        return Err(e).context("UART read error");
                    }
                }
            }

            let len = pipe.read(&mut buf)?;
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
        } else {
            return Err(anyhow!("Pipe not opened")).context("UART read error");
        }
        Ok(())
    }

    fn read_worker(&self, timeout: Duration) -> Result<()> {
        if self.use_stream {
            self.read_stream(timeout)
        } else {
            self.read_pipe(timeout)
        }
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
            if self.use_stream {
                if let Some(ref ref_stream) = self.stream {
                    ref_stream
                        .borrow_mut()
                        .write_all(std::slice::from_ref(b))
                        .context("UART write error")?;
                } else {
                    return Err(anyhow!("TCP socket not connected")).context("UART write error");
                }
            } else if let Some(ref ref_pipe) = self.pipe {
                ref_pipe
                    .borrow_mut()
                    .write_all(std::slice::from_ref(b))
                    .context("UART write error")?;
            } else {
                return Err(anyhow!("Pipe not opened")).context("UART write error");
            }
        }
        Ok(())
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        if self.use_stream {
            if let Some(ref ref_stream) = self.stream {
                let mut buf = [0u8; 1];
                let mut stream = ref_stream.borrow_mut();

                let result = stream.set_nonblocking(true);
                match result {
                    Ok(_) => {}
                    Err(e) => {
                        return Err(e).context("UART reset error");
                    }
                }

                while let Ok(size) = stream.read(&mut buf) {
                    if size != buf.len() {
                        break;
                    }
                }
            } else {
                return Err(anyhow!("TCP socket not connected")).context("UART reset error");
            }
        // TODO: Seek on pipe causes error. Find a different method for draining pipe
        } else if let Some(ref _ref_pipe) = self.pipe {
            //ref_pipe.borrow_mut().seek(SeekFrom::End(0))?;
        } else {
            return Err(anyhow!("Pipe not opened")).context("UART reset error");
        }
        Ok(())
    }
}
