// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::rc::Rc;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::cw310::usb::Backend;
use crate::transport::Result;

pub struct CW310GpioPin {
    device: Rc<RefCell<Backend>>,
    pinname: String,
}

impl CW310GpioPin {
    pub fn open(backend: Rc<RefCell<Backend>>, pinname: String) -> Result<Self> {
        Ok(Self {
            device: backend,
            pinname,
        })
    }
}

impl GpioPin for CW310GpioPin {
    fn read(&self) -> Result<bool> {
        let usb = self.device.borrow();
        let pin = usb.pin_get_state(&self.pinname)?;
        Ok(pin != 0)
    }

    fn write(&self, value: bool) -> Result<()> {
        let usb = self.device.borrow();
        usb.pin_set_state(&self.pinname, value)?;
        Ok(())
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        let usb = self.device.borrow();
        match mode {
            PinMode::Input => usb.pin_set_output(&self.pinname, false)?,
            PinMode::PushPull => usb.pin_set_output(&self.pinname, true)?,
            PinMode::OpenDrain => return Err(GpioError::UnsupportedPinMode(mode).into()),
        }
        Ok(())
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        match mode {
            PullMode::None => Ok(()),
            _ => Err(GpioError::UnsupportedPullMode(mode).into()),
        }
    }
}
