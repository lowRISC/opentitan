// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::rc::Rc;

use crate::io::gpio::GpioPin;
use crate::transport::hyperdebug::{Flavor, Inner, StandardFlavor, VID_GOOGLE};
use crate::transport::{TransportError, TransportInterfaceType};

// The GSC has some capability to control GPIO lines inside a Chromebook, and to program the AP
// firmware flash chip via SPI.  This "flavor" allows OpenTitanTool to access those capabilities.
pub struct Ti50Flavor {}

impl Ti50Flavor {
    const PID_TI50: u16 = 0x504a;
}

impl Flavor for Ti50Flavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        StandardFlavor::gpio_pin(inner, pinname)
    }

    fn spi_index(_inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
        if instance == "AP" {
            return Ok((super::spi::USB_SPI_REQ_ENABLE_AP, 0));
        } else if instance == "EC" {
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
        Self::PID_TI50
    }
}
