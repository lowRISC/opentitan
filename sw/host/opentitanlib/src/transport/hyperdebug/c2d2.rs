// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;

use crate::bail;
use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::transport::hyperdebug::{Flavor, Inner, StandardFlavor, VID_GOOGLE};
use crate::transport::{Result, TransportError};

/// The C2D2 (Case Closed Debugging Debugger) is used to bring up GSC and EC chips sitting
/// inside a Chrome OS devices, such that those GSC chips can provide Case Closed Debugging
/// support to allow bringup of the rest of the Chrome OS device.  C2D2 devices happen to speak
/// almost exactly the same USB protocol as HyperDebug.  This `Flavor` implementation defines
/// the few deviations: USB PID value, and the handling of GSC reset signal.
pub struct C2d2Flavor {}

impl C2d2Flavor {
    const PID_C2D2: u16 = 0x5041;
}

impl Flavor for C2d2Flavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        if pinname == "SPIVREF_RSVD_H1VREF_H1_RST_ODL" {
            return Ok(Rc::new(C2d2ResetPin::open(inner)?));
        }
        StandardFlavor::gpio_pin(inner, pinname)
    }

    fn get_default_usb_vid() -> u16 {
        VID_GOOGLE
    }

    fn get_default_usb_pid() -> u16 {
        Self::PID_C2D2
    }
}

pub struct C2d2ResetPin {
    inner: Rc<Inner>,
}

impl C2d2ResetPin {
    pub fn open(inner: &Rc<Inner>) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(inner),
        })
    }
}

impl GpioPin for C2d2ResetPin {
    /// Reads the value of the the reset pin.
    fn read(&self) -> Result<bool> {
        let mut result: Result<bool> = Err(TransportError::CommunicationError(
            "No output from gpioget".to_string(),
        ));
        self.inner
            .execute_command("gpioget SPIVREF_RSVD_H1VREF_H1_RST_ODL", |line| {
                result = Ok(line.trim_start().starts_with("1"))
            })?;
        result
    }

    /// Sets the value of the GPIO reset pin by means of the special h1_reset command.
    fn write(&self, value: bool) -> Result<()> {
        self.inner
            .execute_command(&format!("h1_reset {}", if value { 0 } else { 1 }), |_| {})?;
        Ok(())
    }

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, _mode: PinMode) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }

    /// Sets the weak pull resistors of the GPIO pin.
    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }
}
