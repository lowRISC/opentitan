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
mod coverage;
#[cfg(test)]
mod coverage_test;
pub mod ext;
mod logged;
pub use broadcast::Broadcaster;
pub use buf::Buffered;
pub use coverage::CoverageMiddleware;
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

    /// Returns a reference to the coverage extraction interface if supported.
    fn as_coverage_console(&self) -> Option<&dyn CoverageConsole> {
        None
    }
}

/// Interface for objects that can wait for coverage extraction to complete.
pub trait CoverageConsole {
    /// Returns the number of coverage blocks processed (finished or skipped).
    fn coverage_blocks_processed(&self) -> usize;
}
