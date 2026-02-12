// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Mutex;
use std::task::{Context, Poll, ready};

use anyhow::Result;

use super::ConsoleDevice;
use crate::io::uart::{FlowControl, Parity, Uart};

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

impl<T: ConsoleDevice> ConsoleDevice for Buffered<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
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

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.inner.write(buf)
    }
}

impl<T: Uart> Uart for Buffered<T> {
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
        let mut buffer = self.buffer.lock().unwrap();
        buffer.offset = 0;
        buffer.len = 0;

        self.inner.clear_rx_buffer()?;
        Ok(())
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
