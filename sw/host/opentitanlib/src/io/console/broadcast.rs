// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, ready};
use std::time::Duration;

use anyhow::Result;

use super::{ConsoleDevice, ConsoleExt};
use crate::io::uart::{FlowControl, Parity, Uart};

/// Broadcast UART recevied data to multiple users.
///
/// Normally, if there are multiple users of `UART`, they share the same buffer (most commonly the kernel buffer).
/// This means that only one user can read a specific piece of data at a time. `Broadcaster` ensures that all clone
/// of it can receive all data.
pub struct Broadcaster<T> {
    inner: Arc<Mutex<BroadcasterInner<T>>>,
    index: usize,
}

impl<T> Clone for Broadcaster<T> {
    fn clone(&self) -> Self {
        let mut inner = self.inner.lock().unwrap();
        let pos = inner.reader_pos[self.index];
        let index = inner.add_reader(pos);
        Self {
            inner: self.inner.clone(),
            index,
        }
    }
}

impl<T> Drop for Broadcaster<T> {
    fn drop(&mut self) {
        let mut inner = self.inner.lock().unwrap();

        // Remove the reader position for this clone.
        // As this array can be sparse, remove all trailing sparse elements as a compactation step.
        inner.reader_pos[self.index] = None;
        while let Some(None) = inner.reader_pos.last() {
            inner.reader_pos.pop();
        }

        // Dropping a broadcaster instance may cause the buffer to be shrinkable.
        inner.shrink();
    }
}

struct BroadcasterInner<T> {
    /// Data received. Dequeing of a specific byte is not possible until all readers have consumed it.
    buffer: VecDeque<u8>,
    /// Reader positions. Each clone of broadcaster occupies a specific index.
    reader_pos: Vec<Option<usize>>,
    /// Inner instance to read from.
    inner: T,
}

impl<T> BroadcasterInner<T> {
    fn add_reader(&mut self, pos: Option<usize>) -> usize {
        // Add a new position to the list. Try to use a freed index preferrably (i.e. None).
        let none_index = self.reader_pos.iter().position(|x| x.is_none());
        if let Some(index) = none_index {
            self.reader_pos[index] = pos;
            index
        } else {
            let index = self.reader_pos.len();
            self.reader_pos.push(pos);
            index
        }
    }

    fn count(&self) -> usize {
        self.reader_pos.iter().filter(|x| x.is_some()).count()
    }

    fn shrink(&mut self) {
        // Now go through all reader_pos to see if we can drop some buffer now.
        let Some(min_pos) = self.reader_pos.iter().filter_map(|x| *x).min() else {
            // Dropped to 0 strong readers.
            self.buffer.clear();
            return;
        };
        self.buffer.drain(..min_pos);

        self.reader_pos
            .iter_mut()
            .filter_map(|x| x.as_mut())
            .for_each(|x| *x -= min_pos);
    }
}

impl<T> Broadcaster<T> {
    pub fn new(inner: T) -> Broadcaster<T> {
        Self {
            inner: Arc::new(Mutex::new(BroadcasterInner {
                buffer: VecDeque::new(),
                reader_pos: vec![Some(0)],
                inner,
            })),
            index: 0,
        }
    }

    /// Obtain a weak instance of this broadcaster that would not consume data.
    pub fn downgrade(&self) -> WeakBroadcaster<T> {
        WeakBroadcaster {
            inner: self.inner.clone(),
        }
    }
}

impl<T: ConsoleDevice> ConsoleDevice for Broadcaster<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        let mut inner = self.inner.lock().unwrap();

        let current_pos = inner.reader_pos[self.index].unwrap();
        if current_pos < inner.buffer.len() {
            // Still more data to read from the buffer.
            // Do some reading first.
            let (front, back) = inner.buffer.as_slices();

            let front_skip = std::cmp::min(current_pos, front.len());
            let front_copy = std::cmp::min(front.len() - front_skip, buf.len());
            buf[..front_copy].copy_from_slice(&front[front_skip..][..front_copy]);

            let back_skip = current_pos.saturating_sub(front_skip);
            let back_copy = std::cmp::min(back.len() - back_skip, buf.len() - front_copy);
            buf[front_copy..][..back_copy].copy_from_slice(&back[back_skip..][..back_copy]);

            let copy_len = front_copy + back_copy;
            *inner.reader_pos[self.index].as_mut().unwrap() += copy_len;

            inner.shrink();
            return Poll::Ready(Ok(copy_len));
        }

        let len = ready!(inner.inner.poll_read(cx, buf))?;

        // We've read some more data. If there're other readers, we need to push to the buffer.
        let total_readers = inner.count();
        if total_readers != 1 {
            inner.buffer.extend(&buf[..len]);
            *inner.reader_pos[self.index].as_mut().unwrap() += len;
        }

        Poll::Ready(Ok(len))
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.inner.lock().unwrap().inner.write(buf)
    }
}

impl<T: Uart> Uart for Broadcaster<T> {
    fn get_baudrate(&self) -> Result<u32> {
        self.inner.lock().unwrap().inner.get_baudrate()
    }

    fn set_baudrate(&self, baudrate: u32) -> Result<()> {
        self.inner.lock().unwrap().inner.set_baudrate(baudrate)
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        self.inner.lock().unwrap().inner.get_flow_control()
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        self.inner
            .lock()
            .unwrap()
            .inner
            .set_flow_control(flow_control)
    }

    fn get_device_path(&self) -> Result<String> {
        self.inner.lock().unwrap().inner.get_device_path()
    }

    fn clear_rx_buffer(&self) -> Result<()> {
        // If we're the only user, clear the inner buffer.
        {
            let inner = self.inner.lock().unwrap();
            if inner.count() == 1 {
                inner.inner.clear_rx_buffer()?;
                return Ok(());
            }
        }

        // If we're not the only user, then we cannot clear RX buffer from `inner`
        // as it disrupts other readers. Just do a read w/ timeout to clear out.
        const TIMEOUT: Duration = Duration::from_millis(5);
        let mut buf = [0u8; 256];
        while self.read_timeout(&mut buf, TIMEOUT)? > 0 {}
        Ok(())
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        self.inner.lock().unwrap().inner.set_parity(parity)
    }

    fn get_parity(&self) -> Result<Parity> {
        self.inner.lock().unwrap().inner.get_parity()
    }

    fn set_break(&self, enable: bool) -> Result<()> {
        self.inner.lock().unwrap().inner.set_break(enable)
    }
}

/// `Broadcaster` but does not actually read data.
///
/// This copy can be used to create proper `Broadcaster`, however it does not create
/// buffer bloat as data does not need to be kept for this copy.
pub struct WeakBroadcaster<T> {
    inner: Arc<Mutex<BroadcasterInner<T>>>,
}

impl<T> Clone for WeakBroadcaster<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T> WeakBroadcaster<T> {
    /// Obtain a `Broadcaster` that can receive console data from this weak instance.
    pub fn upgrade(&self) -> Broadcaster<T> {
        let mut inner = self.inner.lock().unwrap();
        // When upgrading from a weak broadcaster, historic data doesn't matter.
        let pos = inner.buffer.len();
        let index = inner.add_reader(Some(pos));
        Broadcaster {
            inner: self.inner.clone(),
            index,
        }
    }
}
