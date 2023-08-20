// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::app::config;
use crate::app::{PinStrapping, TransportWrapper};
use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::io::i2c::{self, Bus};
use crate::io::ioexpander::IoExpander;
use crate::transport::TransportError;

use anyhow::{bail, Result};
use std::rc::Rc;
use std::vec::Vec;

/// Represents a particular SX1503 IO expander chip, with information about how to access it
/// through a backend transport.
struct Sx1503 {
    mux_strapping: Option<PinStrapping>,
    i2c_bus: Rc<dyn Bus>,
    i2c_addr: u8,
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
enum Sx1503Registers {
    DataB = 0x00,
    DataA = 0x01,
    DirB = 0x02,
    DirA = 0x03,
    PullUpB = 0x04,
    PullUpA = 0x05,
    PullDownB = 0x06,
    PullDownA = 0x07,
    InterruptMaskB = 0x08,
    InterruptMaskA = 0x09,
    SenseHighB = 0x0A,
    SenseHighA = 0x0B,
    SenseLowB = 0x0C,
    SenseLowA = 0x0D,
    InterruptSourceB = 0x0E,
    InterruptSourceA = 0x0F,
    EventStatusB = 0x10,
    EventStatusA = 0x11,
    PLDModeB = 0x20,
    PLDModeA = 0x21,
    PLDTable0B = 0x22,
    PLDTable0A = 0x23,
    PLDTable1B = 0x24,
    PLDTable1A = 0x25,
    PLDTable2B = 0x26,
    PLDTable2A = 0x27,
    PLDTable3B = 0x28,
    PLDTable3A = 0x29,
    PLDTable4B = 0x2A,
    PLDTable4A = 0x2B,
    Advanced = 0xAD,
}

impl Sx1503 {
    fn apply_mux_strapping(&self) -> Result<()> {
        if let Some(ref strapping) = self.mux_strapping {
            strapping.apply()?
        }
        Ok(())
    }

    fn remove_mux_strapping(&self) -> Result<()> {
        if let Some(ref strapping) = self.mux_strapping {
            strapping.remove()?
        }
        Ok(())
    }

    fn read_register(&self, addr: Sx1503Registers) -> Result<u8> {
        let mut val: u8 = 0;
        self.i2c_bus.run_transaction(
            Some(self.i2c_addr),
            &mut [
                i2c::Transfer::Write(&[addr as u8]),
                i2c::Transfer::Read(std::slice::from_mut(&mut val)),
            ],
        )?;
        Ok(val)
    }

    fn write_register(&self, addr: Sx1503Registers, data: u8) -> Result<()> {
        self.i2c_bus.run_transaction(
            Some(self.i2c_addr),
            &mut [i2c::Transfer::Write(&[addr as u8, data])],
        )?;
        Ok(())
    }

    fn set_or_clear_bit(&self, addr: Sx1503Registers, bit_no: u8, value: bool) -> Result<()> {
        let val = self.read_register(addr)?;
        let val = val & !(1 << bit_no) | (if value { 1 << bit_no } else { 0 });
        self.write_register(addr, val)?;
        Ok(())
    }
}

/// Represents a single pin of a particular SX1503 IO expander chip.
struct Sx1503Pin {
    sx1503: Rc<Sx1503>,
    pin_no: u8,
}

impl Sx1503Pin {
    fn new(sx1503: Rc<Sx1503>, pin_no: u8) -> Self {
        Self { sx1503, pin_no }
    }
}

impl GpioPin for Sx1503Pin {
    fn read(&self) -> Result<bool> {
        self.sx1503.apply_mux_strapping()?;
        let val = self.sx1503.read_register(if self.pin_no < 8 {
            Sx1503Registers::DataA
        } else {
            Sx1503Registers::DataB
        })?;
        self.sx1503.remove_mux_strapping()?;
        Ok(val & (1 << (self.pin_no & 0x07)) != 0)
    }

    fn write(&self, value: bool) -> Result<()> {
        self.set(None, Some(value), None, None)
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.set(Some(mode), None, None, None)
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.set(None, None, Some(mode), None)
    }

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> Result<()> {
        if analog_value.is_some() {
            bail!(TransportError::UnsupportedOperation);
        }
        if let (None, None, None) = (mode, value, pull) {
            return Ok(());
        }
        self.sx1503.apply_mux_strapping()?;
        if let Some(value) = value {
            self.sx1503.set_or_clear_bit(
                if self.pin_no < 8 {
                    Sx1503Registers::DataA
                } else {
                    Sx1503Registers::DataB
                },
                self.pin_no & 0x07,
                value,
            )?;
        }
        if let Some(pull) = pull {
            let (up, down) = match pull {
                PullMode::None => (false, false),
                PullMode::PullUp => (true, false),
                PullMode::PullDown => (false, true),
            };
            self.sx1503.set_or_clear_bit(
                if self.pin_no < 8 {
                    Sx1503Registers::PullUpA
                } else {
                    Sx1503Registers::PullUpB
                },
                self.pin_no & 0x07,
                up,
            )?;
            self.sx1503.set_or_clear_bit(
                if self.pin_no < 8 {
                    Sx1503Registers::PullDownA
                } else {
                    Sx1503Registers::PullDownB
                },
                self.pin_no & 0x07,
                down,
            )?;
        }
        if let Some(mode) = mode {
            let direction = match mode {
                PinMode::Input => true,
                PinMode::PushPull => false,
                _ => return Err(GpioError::UnsupportedPinMode(mode).into()),
            };
            self.sx1503.set_or_clear_bit(
                if self.pin_no < 8 {
                    Sx1503Registers::DirA
                } else {
                    Sx1503Registers::DirB
                },
                self.pin_no & 0x07,
                direction,
            )?;
        }
        self.sx1503.remove_mux_strapping()?;
        Ok(())
    }
}

/// Creates an instance of `IoExpander` to represent a SX1503 chip as specified in the given
/// configuration declaration section.
pub fn create(
    conf: &config::IoExpander,
    transport_wrapper: &TransportWrapper,
) -> Result<IoExpander> {
    // Look up I2C bus and strappings, create Sx1503 struct.
    let Some(ref i2c_bus) = conf.i2c_bus else {
        bail!("Missing i2c bus numer");
    };
    let Some(i2c_addr) = conf.i2c_address else {
        bail!("Missing i2c addressr");
    };
    let mux_strapping = if let Some(ref name) = conf.mux_strapping {
        Some(transport_wrapper.pin_strapping(name)?)
    } else {
        None
    };
    let sx1503 = Rc::new(Sx1503 {
        mux_strapping,
        i2c_bus: transport_wrapper.i2c(i2c_bus)?,
        i2c_addr,
    });

    // Create 16 pins each with a shared reference to the struct created above.
    let mut pins: Vec<Rc<dyn GpioPin>> = Vec::new();
    for i in 0..16 {
        pins.push(Rc::new(Sx1503Pin::new(sx1503.clone(), i)));
    }
    Ok(IoExpander { pins })
}
