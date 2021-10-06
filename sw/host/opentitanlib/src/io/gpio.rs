// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use structopt::clap::arg_enum;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum GpioError {
    #[error("Invalid GPIO pin name {0}")]
    InvalidPinName(String),
    #[error("Invalid GPIO pin number {0}")]
    InvalidPinNumber(u8),
    #[error("Invalid GPIO pin direction: {0}")]
    InvalidPinDirection(u8),
}

arg_enum! {
    /// Direction for I/O pins.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum PinDirection {
        Input,
        Output,
    }
}

/// A trait which represents a single GPIO pin.
pub trait GpioPin {
    /// Reads the value of the the GPIO pin.
    fn read(&self) -> Result<bool>;

    /// Sets the value of the GPIO pin to `value`.
    fn write(&self, value: bool) -> Result<()>;

    /// Sets the `direction` of the GPIO pin as input or output.
    fn set_direction(&self, direction: PinDirection) -> Result<()>;
}
