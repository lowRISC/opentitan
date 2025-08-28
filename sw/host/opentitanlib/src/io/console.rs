// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use thiserror::Error;

use crate::impl_serializable_error;
use crate::io::gpio::GpioPin;

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
    fn console_poll_read(
        &self,
        _cx: &mut std::task::Context<'_>,
        _buf: &mut [u8],
    ) -> std::task::Poll<Result<usize>> {
        Err(ConsoleError::UnsupportedError(
            "console_poll_read() not implemented.".into(),
        ))?
    }

    /// Writes console input data to the UART (used when this UART is the console device).
    fn console_write(&self, _buf: &[u8]) -> Result<()> {
        Err(ConsoleError::UnsupportedError("console_write() not implemented.".into()).into())
    }

    fn set_break(&self, _enable: bool) -> Result<()> {
        Err(ConsoleError::GenericError("break unsupported".into()).into())
    }

    /// Query if TX-ready pin non-polling mode is supported.
    fn get_tx_ready_pin(&self) -> Result<Option<&Rc<dyn GpioPin>>> {
        Ok(None)
    }
}
