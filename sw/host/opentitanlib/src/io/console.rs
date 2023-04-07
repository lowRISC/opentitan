// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use thiserror::Error;

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
}
