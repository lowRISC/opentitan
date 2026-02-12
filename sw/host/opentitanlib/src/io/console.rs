// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::task::{Context, Poll};

use anyhow::Result;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::impl_serializable_error;

pub mod broadcast;
mod buf;
pub mod ext;
mod logged;
pub use broadcast::Broadcaster;
pub use buf::Buffered;
pub use ext::ConsoleExt;
pub use logged::Logged;

/// Errors related to the console interface.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum ConsoleError {
    #[error("Timed Out")]
    TimedOut,
    #[error("{0}")]
    GenericError(String),
}
impl_serializable_error!(ConsoleError);

pub trait ConsoleDevice {
    /// Reads received data into `buf`, returning the number of bytes read.
    ///
    /// If data is not yet ready, `Poll::Pending` will be returned and `cx` would be notified when it's available.
    /// When this function is called with multiple wakers, all wakers should be notified instead of just the last one.
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>>;

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()>;
}

impl<T: ConsoleDevice + ?Sized> ConsoleDevice for &T {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        T::poll_read(self, cx, buf)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        T::write(self, buf)
    }
}

impl<T: ConsoleDevice + ?Sized> ConsoleDevice for std::rc::Rc<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        T::poll_read(self, cx, buf)
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        T::write(self, buf)
    }
}
