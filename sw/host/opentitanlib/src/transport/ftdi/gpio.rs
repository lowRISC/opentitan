// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use embedded_hal::digital::{InputPin, OutputPin};
use ftdi_embedded_hal as ftdi_hal;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::transport::ftdi::Chip;

#[derive(Default)]
enum PinType {
    Output(ftdi_hal::OutputPin<ftdi::Device>),
    Input(ftdi_hal::InputPin<ftdi::Device>),
    #[default]
    None,
}

pub struct Pin {
    pin: RefCell<PinType>,
    ftdi: Rc<HashMap<ftdi::Interface, ftdi_hal::FtHal<ftdi::Device>>>,
    pinname: String,
}

impl Pin {
    pub fn open<C: Chip>(
        ftdi: &Rc<HashMap<ftdi::Interface, ftdi_hal::FtHal<ftdi::Device>>>,
        pinname: String,
    ) -> Result<Self> {
        Ok(Self {
            pin: RefCell::new(PinType::None),
            ftdi: Rc::clone(ftdi),
            pinname,
        })
    }

    fn map_outpin(&self) -> Result<ftdi_hal::OutputPin<ftdi::Device>> {
        let pinname = self.pinname.to_lowercase();
        let interface = match &pinname[0..1] {
            "a" => ftdi::Interface::A,
            "b" => ftdi::Interface::B,
            "c" => ftdi::Interface::C,
            "d" => ftdi::Interface::D,
            &_ => return Err(GpioError::InvalidPinName(pinname).into()),
        };
        let hal = self
            .ftdi
            .get(&interface)
            .ok_or_else(|| GpioError::InvalidPinName(pinname.clone()))?;

        let pin = match &pinname[1..] {
            "dbus0" => hal.ad0(),
            "dbus1" => hal.ad1(),
            "dbus2" => hal.ad2(),
            "dbus3" => hal.ad3(),
            "dbus4" => hal.ad4(),
            "dbus5" => hal.ad5(),
            "dbus6" => hal.ad6(),
            "dbus7" => hal.ad7(),
            _ => return Err(GpioError::InvalidPinName(self.pinname.to_owned()).into()),
        }?;
        Ok(pin)
    }

    fn map_inpin(&self) -> Result<ftdi_hal::InputPin<ftdi::Device>> {
        let pinname = self.pinname.to_lowercase();
        let interface = match &pinname[0..1] {
            "a" => ftdi::Interface::A,
            "b" => ftdi::Interface::B,
            "c" => ftdi::Interface::C,
            "d" => ftdi::Interface::D,
            &_ => return Err(GpioError::InvalidPinName(pinname).into()),
        };
        let hal = self
            .ftdi
            .get(&interface)
            .ok_or_else(|| GpioError::InvalidPinName(pinname.clone()))?;

        let pin = match &pinname[1..] {
            "dbus0" => hal.adi0(),
            "dbus1" => hal.adi1(),
            "dbus2" => hal.adi2(),
            "dbus3" => hal.adi3(),
            "dbus4" => hal.adi4(),
            "dbus5" => hal.adi5(),
            "dbus6" => hal.adi6(),
            "dbus7" => hal.adi7(),
            _ => return Err(GpioError::InvalidPinName(self.pinname.to_owned()).into()),
        }?;
        Ok(pin)
    }
}

impl GpioPin for Pin {
    fn read(&self) -> Result<bool> {
        let mut pin = self.pin.borrow_mut();
        match *pin {
            PinType::Input(ref mut pin) => Ok(pin.is_high()?),
            _ => Err(GpioError::InvalidPinMode(0).into()),
        }
    }

    fn write(&self, value: bool) -> Result<()> {
        let mut pin = self.pin.borrow_mut();
        if let PinType::Output(ref mut pin) = *pin {
            if value {
                pin.set_high()?;
            } else {
                pin.set_low()?;
            }
            return Ok(());
        };
        Err(GpioError::InvalidPinMode(0).into())
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        let mut pin = self.pin.borrow_mut();
        *pin = match (&*pin, mode) {
            (PinType::None, PinMode::Input) => PinType::Input(self.map_inpin()?),
            (PinType::None, PinMode::PushPull | PinMode::OpenDrain) => {
                PinType::Output(self.map_outpin()?)
            }
            _ => return Ok(()),
        };
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        Ok(())
    }

    fn get_internal_pin_name(&self) -> Option<&str> {
        Some(&self.pinname)
    }
}
