// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::os::fd::BorrowedFd;
use std::task::{Context, Poll, Waker, ready};
use std::time::Duration;

use anyhow::{Context as _, Result};

use super::{FlowControl, Parity, Uart};
use crate::io::console::ConsoleDevice;

/// Add software flow control to a UART device.
///
/// Flow control is performed using XON/XOFF bytes.
pub struct SoftwareFlowControl<T> {
    inner: T,
    flow_control: Cell<FlowControl>,
    rxbuf: RefCell<VecDeque<u8>>,
}

impl<T: Uart> SoftwareFlowControl<T> {
    /// Open the given serial device, such as `/dev/ttyUSB0`.
    pub fn new(inner: T) -> Self {
        SoftwareFlowControl {
            inner,
            flow_control: Cell::new(FlowControl::None),
            rxbuf: RefCell::default(),
        }
    }

    /// Attempt to read more data into the buffer, and handle flow control characters.
    ///
    /// This may not add more data to the buffer if all characters are flow control.
    fn poll_read_to_buffer(&self, cx: &mut Context<'_>) -> Poll<Result<()>> {
        let mut buf = [0u8; 256];
        let len = ready!(self.inner.poll_read(cx, &mut buf)).context("UART read error")?;

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
        Poll::Ready(Ok(()))
    }
}

impl<T: Uart> ConsoleDevice for SoftwareFlowControl<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        let mut rxbuf = self.rxbuf.borrow_mut();

        while rxbuf.is_empty() {
            drop(rxbuf);
            ready!(self.poll_read_to_buffer(cx))?;
            rxbuf = self.rxbuf.borrow_mut();
        }

        // `VecDeque` can be viewed as two slices.
        let (front, back) = rxbuf.as_slices();

        let front_copy = std::cmp::min(buf.len(), front.len());
        buf[..front_copy].copy_from_slice(&front[..front_copy]);

        let back_copy = std::cmp::min(buf.len() - front_copy, back.len());
        buf[front_copy..][..back_copy].copy_from_slice(&back[..back_copy]);

        let copy_len = front_copy + back_copy;
        rxbuf.drain(..copy_len);
        Poll::Ready(Ok(copy_len))
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        if self.flow_control.get() == FlowControl::None {
            return self.inner.write(buf);
        }

        // The constant of 10 is approximately 10 uart bit times per byte.
        let pacing = Duration::from_nanos(10 * 1_000_000_000u64 / (self.get_baudrate()? as u64));
        log::debug!(
            "flow control: {:?}, pacing = {:?}",
            self.flow_control.get(),
            pacing
        );

        for b in buf.iter() {
            // If flow control is enabled, read data from the input stream and
            // process the flow control chars.
            loop {
                let _ = self.poll_read_to_buffer(&mut Context::from_waker(Waker::noop()))?;
                // If we're ok to send, then break out of the flow-control loop and send the data.
                if self.flow_control.get() == FlowControl::Resume {
                    break;
                }
                // Sleep one uart character time to avoid busy polling the UART.
                std::thread::sleep(pacing);
            }
            self.inner
                .write(std::slice::from_ref(b))
                .context("UART write error")?;
            // Sleep one uart character time after writing to the uart to pace characters into the
            // usb-serial device so that we don't fill any device-internal buffers.  The Chip Whisperer board (for
            // example) appears to have a large internal buffer that will keep transmitting to OT
            // even if an XOFF is sent.
            std::thread::sleep(pacing);
        }
        Ok(())
    }
}

impl<T: Uart> Uart for SoftwareFlowControl<T> {
    fn get_baudrate(&self) -> Result<u32> {
        self.inner.get_baudrate()
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.inner.set_baudrate(baudrate)
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        Ok(self.flow_control.get())
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.flow_control.set(match flow_control {
            false => FlowControl::None,
            // When flow-control is enabled, assume we haven't
            // already been put into a pause state.
            true => FlowControl::Resume,
        });
        Ok(())
    }

    fn get_device_path(&self) -> Result<String> {
        self.inner.get_device_path()
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.inner.set_parity(parity)
    }

    /// Clears the UART RX buffer.
    fn clear_rx_buffer(&self) -> Result<()> {
        self.rxbuf.borrow_mut().clear();

        // Clear the host input buffer.
        self.inner.clear_rx_buffer()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        self.inner.set_break(enable)
    }

    fn borrow_fd(&self) -> Result<BorrowedFd<'_>> {
        self.inner.borrow_fd()
    }
}
