// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::board::Board;
use anyhow::Result;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::gpio::PinConfiguration;
use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::chip_whisperer::usb::Backend;

pub struct Pin<B: Board> {
    device: Rc<RefCell<Backend<B>>>,
    pinname: String,
    config: PinConfiguration,
}

impl<B: Board> Pin<B> {
    pub fn open(
        backend: Rc<RefCell<Backend<B>>>,
        pinname: String,
        config: PinConfiguration,
    ) -> Result<Self> {
        Ok(Self {
            device: backend,
            pinname,
            config,
        })
    }
}

impl<B: Board> GpioPin for Pin<B> {
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
            _ => return Err(GpioError::UnsupportedPinMode(mode).into()),
        }
        Ok(())
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        match mode {
            PullMode::None => Ok(()),
            _ => Err(GpioError::UnsupportedPullMode(mode).into()),
        }
    }

    fn reset(&self) -> Result<()> {
        self.write(self.config.level.unwrap_or(false))
    }
}
