// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use lazy_static::lazy_static;
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::ultradebug::mpsse;
use crate::transport::ultradebug::Ultradebug;
use crate::transport::{Result, TransportError, WrapInTransportError};
use crate::util::parse_int::ParseInt;
use crate::{collection, ensure};

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

    pub fn pin(&self, pinname: &str) -> Result<UltradebugGpioPin> {
        Ok(UltradebugGpioPin {
            device: self.device.clone(),
            pin_id: self.pin_name_to_number(pinname)?,
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

pub struct UltradebugGpioPin {
    device: Rc<RefCell<mpsse::Context>>,
    pin_id: u8,
}

impl GpioPin for UltradebugGpioPin {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        let bits = self.device.borrow_mut().gpio_get().wrap(TransportError::FtdiError)?;
        Ok(bits & (1 << self.pin_id) != 0)
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.device.borrow_mut().gpio_set(self.pin_id, value).wrap(TransportError::FtdiError)?;
        Ok(())
    }

    /// Sets the `direction` of GPIO `id` as input or output.
    fn set_mode(&self, mode: PinMode) -> Result<()> {
        let direction = match mode {
            PinMode::Input => false,
            PinMode::PushPull => true,
            PinMode::OpenDrain => return Err(GpioError::UnsupportedPinMode(mode).into()),
        };
        self.device
            .borrow_mut()
            .gpio_set_direction(self.pin_id, direction)
            .wrap(TransportError::FtdiError)?;
        Ok(())
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        Err(GpioError::UnsupportedPullMode(mode).into())
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
