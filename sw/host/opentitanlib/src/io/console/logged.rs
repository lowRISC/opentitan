// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::Write;
use std::sync::Mutex;
use std::task::{Context, Poll, ready};
use std::time::SystemTime;

use anyhow::Result;

use super::ConsoleDevice;
use crate::io::uart::{FlowControl, Parity, Uart};

/// Middleware that logs the received data.
pub struct Logged<T> {
    inner: T,
    /// If the next character is the beginning of a line.
    newline: Mutex<bool>,
}

impl<T> Logged<T> {
    pub fn new(inner: T) -> Logged<T> {
        Self {
            inner,
            newline: Mutex::new(true),
        }
    }
}

impl<T: ConsoleDevice> ConsoleDevice for Logged<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        // Establish order between readers, if there are many.
        let mut newline = self.newline.lock().unwrap();
        let len = ready!(self.inner.poll_read(cx, buf))?;

        let mut stdout = std::io::stdout().lock();
        for ch in buf[..len].iter().copied() {
            if *newline {
                let t = humantime::format_rfc3339_millis(SystemTime::now());
                stdout.write_fmt(format_args!("[{}  console]", t))?;
            }

            *newline = ch == b'\n';

            stdout.write_all(std::slice::from_ref(&ch))?;
        }
        stdout.flush()?;

        Poll::Ready(Ok(len))
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.inner.write(buf)
    }
}

impl<T: Uart> Uart for Logged<T> {
    fn get_baudrate(&self) -> Result<u32> {
        self.inner.get_baudrate()
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.inner.set_baudrate(baudrate)
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        self.inner.get_flow_control()
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.inner.set_flow_control(flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        self.inner.get_device_path()
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        *self.newline.lock().unwrap() = true;
        self.inner.clear_rx_buffer()
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.inner.set_parity(parity)
    }

    fn get_parity(&self) -> Result<Parity> {
        self.inner.get_parity()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        self.inner.set_break(enable)
    }
}
