// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Mutex;
use std::task::{Context, Poll, ready};

use anyhow::Result;

use super::ConsoleDevice;
use crate::io::middleware::{ConsoleMiddleware, Middleware, UartMiddleware};
use crate::io::uart::Uart;

/// Console wrapper with receive buffer.
pub struct Buffered<T> {
    inner: T,
    buffer: Mutex<Inner>,
}

struct Inner {
    buffer: Box<[u8; 256]>,
    len: usize,
    offset: usize,
}

impl<T> Buffered<T> {
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            buffer: Mutex::new(Inner {
                buffer: vec![0; 256].try_into().unwrap(),
                len: 0,
                offset: 0,
            }),
        }
    }
}

impl<T: ConsoleDevice> Middleware for Buffered<T> {
    type Inner = T;
    fn inner(&self) -> &T {
        &self.inner
    }
}

impl<T: ConsoleDevice> ConsoleMiddleware for Buffered<T> {
    fn poll_read_impl(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        let mut buffer = self.buffer.lock().unwrap();

        loop {
            if buffer.len != 0 {
                let copy_len = std::cmp::min(buffer.len, buf.len());
                buf[..copy_len].copy_from_slice(&buffer.buffer[buffer.offset..][..copy_len]);
                buffer.offset += copy_len;
                buffer.len -= copy_len;
                return Poll::Ready(Ok(copy_len));
            }

            if buf.len() >= buffer.buffer.len() {
                return self.inner.poll_read(cx, buf);
            }

            buffer.len = ready!(self.inner.poll_read(cx, &mut buffer.buffer[..]))?;
            buffer.offset = 0;
        }
    }
}

impl<T: Uart> UartMiddleware for Buffered<T> {
    fn clear_rx_buffer_impl(&self) -> Result<()> {
        let mut buffer = self.buffer.lock().unwrap();
        buffer.offset = 0;
        buffer.len = 0;

        self.inner.clear_rx_buffer()?;
        Ok(())
    }
}
