// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::gpio::Gpio;
use crate::transport::ultradebug::mpsse;
use crate::transport::ultradebug::Ultradebug;

/// Represents the Ultradebug GPIO pins.
pub struct UltradebugGpio {
    pub device: Rc<RefCell<mpsse::Context>>,
}

impl UltradebugGpio {
    /// Request the upstream SPI bus to tristate so ultradebug may drive the SPI bus (platforms-ultradebug only).
    pub const PIN_SPI_ZB: u32 = 4;
    /// Reset the chip attached to ultradebug.
    pub const PIN_RESET_B: u32 = 5;
    /// Request bootstrap mode on the chip attached to ultradebug.
    pub const PIN_BOOTSTRAP: u32 = 6;
    /// Reset the target system attached to ultradebug (platforms-ultradebug only).
    pub const PIN_TGT_RESET: u32 = 7;

    pub fn open(ultradebug: &Ultradebug) -> Result<Self> {
        Ok(UltradebugGpio {
            device: ultradebug.mpsse(ftdi::Interface::B)?,
        })
    }
}

impl Gpio for UltradebugGpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, id: u32) -> Result<bool> {
        let bits = self.device.borrow_mut().gpio_get()?;
        Ok(bits & (1 << id) != 0)
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: u32, value: bool) -> Result<()> {
        self.device.borrow_mut().gpio_set(id, value)
    }
}
