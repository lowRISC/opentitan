// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use anyhow::Result;
use std::rc::Rc;

pub struct GpioPinWrapper {
    underlying: Rc<dyn GpioPin>,
    invert: bool,
}

impl GpioPinWrapper {
    pub fn new(underlying: Rc<dyn GpioPin>, invert: bool) -> Self {
        Self { underlying, invert }
    }
}

impl GpioPin for GpioPinWrapper {
    fn read(&self) -> Result<bool> {
        Ok(self.underlying.read()? != self.invert)
    }

    fn write(&self, value: bool) -> Result<()> {
        self.underlying.write(value != self.invert)
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.underlying.set_mode(mode)
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.underlying.set_pull_mode(mode)
    }

    fn analog_read(&self) -> Result<f32> {
        self.underlying.analog_read()
    }

    fn analog_write(&self, volts: f32) -> Result<()> {
        self.underlying.analog_write(volts)
    }

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> Result<()> {
        self.underlying
            .set(mode, value.map(|v| v != self.invert), pull, analog_value)
    }

    fn get_internal_pin_name(&self) -> Option<&str> {
        self.underlying.get_internal_pin_name()
    }
}
