// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

/// A trait which represents a GPIO interface.
pub trait Gpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, id: u32) -> Result<bool>;

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: u32, value: bool) -> Result<()>;
}
