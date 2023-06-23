// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::rc::Rc;

use crate::io::gpio::GpioPin;
use crate::transport::hyperdebug::{Flavor, Inner, StandardFlavor, VID_GOOGLE};
use crate::transport::{TransportError, TransportInterfaceType};

/// The Servo Micro is used to bring up GSC and EC chips sitting inside a computing device, such
/// that those GSC chips can provide Case Closed Debugging support to allow bringup of the rest of
/// the computing device.  Servo devices happen to speak almost exactly the same USB protocol as
/// HyperDebug.  This `Flavor` implementation defines the few deviations: USB PID value, and the
/// handling of OT reset signal.
pub struct ServoMicroFlavor {}

impl ServoMicroFlavor {
    const PID_SERVO_MICRO: u16 = 0x501A;
}

impl Flavor for ServoMicroFlavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        StandardFlavor::gpio_pin(inner, pinname)
    }

    fn spi_index(_inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
        if instance == "AP" {
            return Ok((super::spi::USB_SPI_REQ_ENABLE_AP, 0));
        }
        if instance == "EC" {
            return Ok((super::spi::USB_SPI_REQ_ENABLE_EC, 0));
        }
        bail!(TransportError::InvalidInstance(
            TransportInterfaceType::Spi,
            instance.to_string()
        ))
    }

    fn get_default_usb_vid() -> u16 {
        VID_GOOGLE
    }

    fn get_default_usb_pid() -> u16 {
        Self::PID_SERVO_MICRO
    }
    fn perform_initial_fw_check() -> bool {
        // The servo micro firmware and hyperdebug firmware are different, so do not check.
        false
    }
}
