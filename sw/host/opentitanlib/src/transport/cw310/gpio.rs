// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::gpio::{Gpio, GpioError, PinDirection, StrapConfig};
use crate::transport::cw310::usb::Backend;
use crate::transport::cw310::CW310;

pub struct CW310Gpio {
    device: Rc<RefCell<Backend>>,
}

impl CW310Gpio {
    pub fn open(backend: Rc<RefCell<Backend>>) -> Result<Self> {
        Ok(CW310Gpio { device: backend })
    }
}

impl Gpio for CW310Gpio {
    fn read(&self, id: &str) -> Result<bool> {
        let usb = self.device.borrow();
        let pin = usb.pin_get_state(id)?;
        Ok(pin != 0)
    }

    fn write(&self, id: &str, value: bool) -> Result<()> {
        let usb = self.device.borrow();
        usb.pin_set_state(id, value)?;
        Ok(())
    }

    fn set_direction(&self, id: &str, direction: PinDirection) -> Result<()> {
        let usb = self.device.borrow();
        usb.pin_set_output(id, direction == PinDirection::Output)?;
        Ok(())
    }

    fn drive_reset(&self, reset: bool) -> Result<()> {
        self.write(CW310::PIN_SRST, !reset)
    }

    fn set_strap_pins(&self, strap: StrapConfig) -> Result<()> {
        match strap {
            StrapConfig::None => self.write(CW310::PIN_BOOTSTRAP, false),
            StrapConfig::RomBootstrap => self.write(CW310::PIN_BOOTSTRAP, true),
            _ => Err(GpioError::InvalidStrapConfig(strap).into()),
        }
    }
}
