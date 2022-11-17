// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use structopt::clap::arg_enum;
use thiserror::Error;

use crate::impl_serializable_error;

/// Errors related to the GPIO interface.
#[derive(Debug, Error, Serialize, Deserialize)]
pub enum GpioError {
    #[error("Invalid pin name {0}")]
    InvalidPinName(String),
    #[error("Invalid pin number {0}")]
    InvalidPinNumber(u8),
    /// The current mode of the pin (input) does not support the requested operation (set
    /// level).
    #[error("Invalid mode for pin {0}")]
    InvalidPinMode(u8),
    /// The hardware does not support the requested mode (open drain, pull down input, etc.)
    #[error("Unsupported mode {0} requested")]
    UnsupportedPinMode(PinMode),
    /// The hardware does not support the requested mode (open drain, pull down input, etc.)
    #[error("Unsupported pull mode {0} requested")]
    UnsupportedPullMode(PullMode),
    #[error("Conflicting pin configurations for pin {0}: host:{1}, target:{2}")]
    PinModeConflict(String, String, String),
    #[error("Conflicting pin logic values for pin {0}: host:{1}, target:{2}")]
    PinValueConflict(String, String, String),
    #[error("Undefined pin logic value for pin {0}")]
    PinValueUndefined(String),
    #[error("Generic error: {0}")]
    Generic(String),
}
impl_serializable_error!(GpioError);

arg_enum! {
    /// Mode of I/O pins.
    #[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
    pub enum PinMode {
        Input,
        PushPull,
        WeakPushPull,
        OpenDrain,
    }
}

arg_enum! {
    /// Mode of weak pull (relevant in Input and OpenDrain modes).
    #[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
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
