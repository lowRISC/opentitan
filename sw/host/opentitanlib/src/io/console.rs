// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::time::Duration;
use thiserror::Error;

use super::nonblocking_help::{NoNonblockingHelp, NonblockingHelp};
use crate::impl_serializable_error;

/// Errors related to the console interface.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum ConsoleError {
    #[error("Unsupported: {0}")]
    UnsupportedError(String),
    #[error("{0}")]
    GenericError(String),
}
impl_serializable_error!(ConsoleError);

pub trait ConsoleDevice {
    /// Reads data from the UART to print to the console (used when this UART is the console device).
    fn console_read(&self, _buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        Err(ConsoleError::UnsupportedError("console_read() not implemented.".into()).into())
    }

    /// Writes console input data to the UART (used when this UART is the console device).
    fn console_write(&self, _buf: &[u8]) -> Result<()> {
        Err(ConsoleError::UnsupportedError("console_write() not implemented.".into()).into())
    }

    fn set_break(&self, _enable: bool) -> Result<()> {
        Err(ConsoleError::GenericError("break unsupported".into()).into())
    }

    /// Query if nonblocking mio mode is supported.
    fn supports_nonblocking_read(&self) -> Result<bool> {
        Ok(false)
    }

    /// Switch this `Uart` instance into nonblocking mio mode.  Going
    /// forward, `read()` should only be called after `mio::poll()` has
    /// indicated that the given `Token` is ready.
    fn register_nonblocking_read(
        &self,
        _registry: &mio::Registry,
        _token: mio::Token,
    ) -> Result<()> {
        unimplemented!();
    }

    /// Get the same single `NonblockingHelp` object as from top level
    /// `Transport.nonblocking_help()`.
    fn nonblocking_help(&self) -> Result<Rc<dyn NonblockingHelp>> {
        Ok(Rc::new(NoNonblockingHelp))
    }
}
