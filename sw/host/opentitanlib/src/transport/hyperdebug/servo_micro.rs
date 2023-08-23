// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::rc::Rc;

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::transport::hyperdebug::{Flavor, Inner, StandardFlavor, VID_GOOGLE};
use crate::transport::{TransportError, TransportInterfaceType};

/// The Servo Micro is used to bring up GSC and EC chips sitting inside a computing device, such
/// that those GSC chips can provide Case Closed Debugging support to allow bringup of the rest of
/// the computing device. Servo devices happen to speak almost exactly the same USB protocol as
/// HyperDebug. This `Flavor` implementation defines the few deviations: USB PID value, and the
/// handling of OT reset signal.
pub struct ServoMicroFlavor;

impl ServoMicroFlavor {
    const PID_SERVO_MICRO: u16 = 0x501A;
}

impl Flavor for ServoMicroFlavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        if pinname == "IO_EXP_16" {
            return Ok(Rc::new(ServoMicroResetPin::open(inner, false)?));
        }
        StandardFlavor::gpio_pin(inner, pinname)
    }

    fn spi_index(_inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
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

/// A register for the IO expander on the servo micro i2c bus
#[derive(Copy, Clone)]
#[repr(u8)]
enum IoExpanderRegister {
    /// Input values for Port 1 pins. `1'b` represents a logic high.
    Input1 = 1,
    /// Output values for Port 1 pins. `1'b` represents a logic high. Note that if `FloatPin1` bit
    /// is set to high, then output pin value is not used.
    Output1 = 3,
    /// Specifies if the IO expander is floating or driving the pin. `1'b` represents the IO
    /// expander producing a HighZ floating state on the pin, and `0'b` represents the IO expander
    /// driving the value from the `Output1` register on the pin.
    FloatPin1 = 7,
}

/// Handles the specialized IO expander logic to read and write to the OT reset pin
pub struct ServoMicroResetPin {
    inner: Rc<Inner>,
    default_level: bool,
}

impl ServoMicroResetPin {
    /// The target reset pin mask for `IoExpanderRegister `
    const RESET_PIN_MASK: u8 = 1 << 6;

    pub fn open(inner: &Rc<Inner>, default_level: bool) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(inner),
            default_level,
        })
    }

    /// Returns the raw value of `IoExpanderRegister`.
    fn read_reg(&self, reg: IoExpanderRegister) -> Result<u8> {
        let cmd = format!("i2cxfer r 0 0x20 {}", reg as u8);
        let line = self
            .inner
            .cmd_one_line_output(&cmd)
            .map_err(|_| TransportError::CommunicationError(format!("No output from {cmd}")))?;
        let Some(Ok(val)) = line
            .split_ascii_whitespace()
            .last()
            .map(|s| s.trim_matches(|c| !char::is_ascii_digit(&c)).parse::<u8>())
        else {
            bail!(TransportError::CommunicationError(format!(
                "Bad i2cxfer output: '{line}'"
            )))
        };
        Ok(val)
    }

    /// Writes the entire raw value to a `IoExpanderRegister`.
    fn write_reg(&self, reg: IoExpanderRegister, val: u8) -> Result<()> {
        let cmd = format!("i2cxfer w 0 0x20 {} {val}", reg as u8);
        self.inner.cmd_no_output(&cmd)
    }

    /// Reads only the value of OT reset pin for the specified `IoExpanderRegister`.
    fn read_pin(&self, reg: IoExpanderRegister) -> Result<bool> {
        self.read_reg(reg)
            .map(|val| val & Self::RESET_PIN_MASK != 0)
    }

    /// Writes only the value of the OT reset pin for the specified `IoExpanderRegister` via
    /// read-modify-write operation on the `IoExpanderRegister`.
    fn write_pin(&self, reg: IoExpanderRegister, val: bool) -> Result<()> {
        let read_val = self.read_reg(reg)?;
        let write_val = if val {
            read_val | Self::RESET_PIN_MASK
        } else {
            read_val & !Self::RESET_PIN_MASK
        };
        // Only write if the value isn't already what we want
        if read_val != write_val {
            self.write_reg(reg, write_val)
        } else {
            Ok(())
        }
    }
}

impl GpioPin for ServoMicroResetPin {
    /// Reads the value of the reset pin.
    fn read(&self) -> Result<bool> {
        self.read_pin(IoExpanderRegister::Input1)
    }

    /// Sets the value of the GPIO reset pin by means of multiple io expander commands
    fn write(&self, value: bool) -> Result<()> {
        // We don't need to write to the output register if we are just going to float the pin
        if !value {
            self.write_pin(IoExpanderRegister::Output1, false)?;
        }
        self.write_pin(IoExpanderRegister::FloatPin1, value)
    }

    fn set_mode(&self, _mode: PinMode) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }

    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }

    fn reset(&self) -> Result<()> {
        self.write(self.default_level)
    }
}
