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
    #[error("Invalid strap configuration: {0:?}")]
    InvalidStrapConfig(StrapConfig),
}

arg_enum! {
    /// Direction for I/O pins.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum PinDirection {
        Input,
        Output,
    }
}

/// Settings for pin straps.  Not all backends support all settings.
#[derive(Clone, Copy, Debug)]
pub enum StrapConfig {
    None,
    RomBootstrap,
    Custom(u8),
}

/// A trait which represents a GPIO interface.
pub trait Gpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, id: &str) -> Result<bool>;

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: &str, value: bool) -> Result<()>;

    /// Sets the `direction` of GPIO `id` as input or output.
    fn set_direction(&self, id: &str, direction: PinDirection) -> Result<()>;

    /// Drive the reset pin. The `reset` parameter represents whether or not the caller
    /// wants to drive the chip into reset, _not_ the logic-level of the reset pin.
    fn drive_reset(&self, reset: bool) -> Result<()>;

    /// Set the requested strap value to the strapping pins.  Note: not all backends
    /// support all settings.  An unsupported StrapConfig will result in an
    /// `InvalidStrapConfig` error.
    fn set_strap_pins(&self, strap: StrapConfig) -> Result<()>;
}
