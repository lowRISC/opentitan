// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use embedded_hal::digital::OutputPin;
use ftdi_embedded_hal as ftdi_hal;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::ftdi::Chip;

pub struct Pin {
    pin: Rc<RefCell<ftdi_hal::OutputPin<ftdi::Device>>>,
    pinname: String,
}

impl Pin {
    pub fn open<C: Chip>(
        ftdi_interfaces: &HashMap<ftdi::Interface, ftdi_hal::FtHal<ftdi::Device>>,
        pinname: String,
    ) -> Result<Self> {
        let pinname = pinname.to_lowercase();
        let (interface, pin) = pinname.split_at(1);
        let interface = match interface {
            "a" => ftdi::Interface::A,
            "b" => ftdi::Interface::B,
            "c" => ftdi::Interface::C,
            "d" => ftdi::Interface::D,
            &_ => panic!("{}", pinname.clone()),
        };

        let hal = ftdi_interfaces
            .get(&interface)
            .ok_or_else(|| GpioError::InvalidPinName(pinname.clone()))?;
        let pin = match pin {
            "dbus0" => hal.ad0(),
            "dbus1" => hal.ad1(),
            "dbus2" => hal.ad2(),
            "dbus3" => hal.ad3(),
            "dbus4" => hal.ad4(),
            "dbus5" => hal.ad5(),
            "dbus6" => hal.ad6(),
            "dbus7" => hal.ad7(),
            _ => return Err(GpioError::InvalidPinName(pinname).into()),
        }?;

        Ok(Self {
            pin: Rc::new(RefCell::new(pin)),
            pinname,
        })
    }
}

impl GpioPin for Pin {
    fn read(&self) -> Result<bool> {
        Ok(false)
    }

    fn write(&self, value: bool) -> Result<()> {
        if value {
            self.pin.borrow_mut().set_high()?;
        } else {
            self.pin.borrow_mut().set_low()?;
        }
        Ok(())
    }

    fn set_mode(&self, _mode: PinMode) -> Result<()> {
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        Ok(())
    }

    fn get_internal_pin_name(&self) -> Option<&str> {
        Some(&self.pinname)
    }
}
