// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::rc::Rc;

use crate::io::gpio::{GpioPin, PinDirection};
use crate::transport::hyperdebug::{Error, Hyperdebug, Inner};

pub struct HyperdebugGpioPin {
    inner: Rc<Inner>,
    pinname: String,
}

impl HyperdebugGpioPin {
    pub fn open(hyperdebug: &Hyperdebug, pinname: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&hyperdebug.inner),
            pinname: pinname.to_string(),
        };
        Ok(result)
    }
}

impl GpioPin for HyperdebugGpioPin {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        let mut result: Result<bool> =
            Err(Error::CommunicationError("No output from gpioget").into());
        self.inner
            .execute_command(&format!("gpioget {}", &self.pinname), |line| {
                result = Ok(line.trim_start().starts_with("1"))
            })?;
        result
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.inner.execute_command(
            &format!("gpioset {} {}", &self.pinname, if value { 1 } else { 0 }),
            |_| {},
        )
    }

    /// Sets the `direction` of GPIO `id` as input or output.
    fn set_direction(&self, _direction: PinDirection) -> Result<()> {
        unimplemented!()
    }
}
