// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serialport::TTYPort;
use std::cell::{Cell, RefCell};
use std::io::Write;

use crate::io::gpio::{GpioPin, PinMode, PullMode};

/// Pin-like interface for controlling USB VBUS.
pub struct QemuVbusSense {
    pub usbdev: RefCell<TTYPort>,
    pub asserted: Cell<bool>,
}

impl QemuVbusSense {
    pub fn new(usbdev: TTYPort) -> QemuVbusSense {
        QemuVbusSense {
            usbdev: RefCell::new(usbdev),
            asserted: Cell::new(false),
        }
    }
}

impl GpioPin for QemuVbusSense {
    fn read(&self) -> anyhow::Result<bool> {
        Ok(self.asserted.get())
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        if value == self.asserted.get() {
            return Ok(());
        }

        let cmd = if value { "vbus_on" } else { "vbus_off" };
        writeln!(*self.usbdev.borrow_mut(), "{}", cmd)?;

        self.asserted.set(value);

        Ok(())
    }

    fn set_mode(&self, _mode: PinMode) -> anyhow::Result<()> {
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> anyhow::Result<()> {
        Ok(())
    }

    fn set(
        &self,
        _mode: Option<PinMode>,
        value: Option<bool>,
        _pull: Option<PullMode>,
        _analog_value: Option<f32>,
    ) -> anyhow::Result<()> {
        if let Some(value) = value {
            return self.write(value);
        }

        Ok(())
    }
}
