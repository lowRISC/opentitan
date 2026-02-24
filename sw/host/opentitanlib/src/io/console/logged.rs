// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::Write;
use std::sync::Mutex;
use std::task::{Context, Poll, ready};
use std::time::SystemTime;

use anyhow::Result;

use super::ConsoleDevice;
use crate::io::middleware::{ConsoleMiddleware, Middleware, UartMiddleware};
use crate::io::uart::Uart;

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

impl<T: ConsoleDevice> Middleware for Logged<T> {
    type Inner = T;
    fn inner(&self) -> &T {
        &self.inner
    }
}

impl<T: ConsoleDevice> ConsoleMiddleware for Logged<T> {
    fn poll_read_impl(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
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
}

impl<T: Uart> UartMiddleware for Logged<T> {
    fn clear_rx_buffer_impl(&self) -> Result<()> {
        *self.newline.lock().unwrap() = true;
        self.inner.clear_rx_buffer()
    }
}
