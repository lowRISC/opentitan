// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use lazy_static::lazy_static;
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::collection;
use crate::io::gpio::{Gpio, GpioError, PinDirection, StrapConfig};
use crate::transport::ultradebug::mpsse;
use crate::transport::ultradebug::Ultradebug;
use crate::util::parse_int::ParseInt;

/// Represents the Ultradebug GPIO pins.
pub struct UltradebugGpio {
    pub device: Rc<RefCell<mpsse::Context>>,
}

impl UltradebugGpio {
    /// Request the upstream SPI bus to tristate so ultradebug may drive the SPI bus (platforms-ultradebug only).
    pub const PIN_SPI_ZB: u8 = 4;
    /// Reset the chip attached to ultradebug.
    pub const PIN_RESET_B: u8 = 5;
    /// Request bootstrap mode on the chip attached to ultradebug.
    pub const PIN_BOOTSTRAP: u8 = 6;
    /// Reset the target system attached to ultradebug (platforms-ultradebug only).
    pub const PIN_TGT_RESET: u8 = 7;

    const LAST_PIN_NUM: u8 = 7;

    pub fn open(ultradebug: &Ultradebug) -> Result<Self> {
        Ok(UltradebugGpio {
            device: ultradebug.mpsse(ftdi::Interface::B)?,
        })
    }

    /// Given an ultradebug pin name, return its pin number.
    pub fn pin_name_to_number(&self, pinname: &str) -> Result<u8> {
        // If the pinname is an integer, use it; otherwise try to see if it
        // is a symbolic name of a pin.
        if let Ok(pinnum) = u8::from_str(pinname) {
            ensure!(
                pinnum <= UltradebugGpio::LAST_PIN_NUM,
                GpioError::InvalidPinNumber(pinnum)
            );
            return Ok(pinnum);
        }
        let pinname = pinname.to_uppercase();
        let pn = pinname.as_str();
        PIN_NAMES
            .get(pn)
            .copied()
            .ok_or_else(|| GpioError::InvalidPinName(pinname).into())
    }
}

impl Gpio for UltradebugGpio {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self, id: &str) -> Result<bool> {
        let id = self.pin_name_to_number(id)?;
        let bits = self.device.borrow_mut().gpio_get()?;
        Ok(bits & (1 << id) != 0)
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, id: &str, value: bool) -> Result<()> {
        let id = self.pin_name_to_number(id)?;
        self.device.borrow_mut().gpio_set(id, value)
    }

    /// Sets the `direction` of GPIO `id` as input or output.
    fn set_direction(&self, id: &str, direction: PinDirection) -> Result<()> {
        let id = self.pin_name_to_number(id)?;
        self.device
            .borrow_mut()
            .gpio_set_direction(id, direction == PinDirection::Output)
    }

    /// Drive the reset pin. The `reset` parameter represents whether or not the caller
    /// wants to drive the chip into reset, _not_ the logic-level of the reset pin.
    fn drive_reset(&self, reset: bool) -> Result<()> {
        self.write("RESET_B", !reset)
    }

    /// Set the requested strap value to the strapping pins.  Note: not all backends
    /// support all settings.  An unsupported StrapConfig will result in an
    /// `InvalidStrapConfig` error.
    fn set_strap_pins(&self, strap: StrapConfig) -> Result<()> {
        match strap {
            StrapConfig::None => self.write("BOOTSTRAP", false),
            StrapConfig::RomBootstrap => self.write("BOOTSTRAP", true),
            _ => Err(GpioError::InvalidStrapConfig(strap).into()),
        }
    }
}

lazy_static! {
    static ref PIN_NAMES: HashMap<&'static str, u8> = collection! {
        "SPI_ZB" => 4,
        "RESET_B" => 5,
        "BOOTSTRAP" => 6,
        "TGT_RESET" => 7,
    };
}
