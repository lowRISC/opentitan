// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::Deserialize;
use structopt::clap::arg_enum;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum GpioError {
    #[error("Invalid GPIO pin name {0}")]
    InvalidPinName(String),
    #[error("Invalid GPIO pin number {0}")]
    InvalidPinNumber(u8),
    /// The current mode of the pin (input) does not support the requested operation (set
    /// level).
    #[error("Invalid GPIO mode for pin {0}")]
    InvalidPinMode(u8),
    /// The hardware does not support the requested mode (open drain, pull down input, etc.)
    #[error("Unsupported GPIO mode requested")]
    UnsupportedPinMode(),
}

arg_enum! {
    /// Mode of I/O pins.
    #[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
    pub enum PinMode {
        Input,
        PushPull,
        OpenDrain,
    }
}

arg_enum! {
    /// Mode of weak pull (relevant in Input and OpenDrain modes).
    #[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq)]
    pub enum PullMode {
        None,
        PullUp,
        PullDown,
    }
}

/// A trait which represents a single GPIO pin.
pub trait GpioPin {
    /// Reads the value of the the GPIO pin.
    fn read(&self) -> Result<bool>;

    /// Sets the value of the GPIO pin to `value`.
    fn write(&self, value: bool) -> Result<()>;

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, mode: PinMode) -> Result<()>;

    /// Sets the weak pull resistors of the GPIO pin.
    fn set_pull_mode(&self, mode: PullMode) -> Result<()>;
}
