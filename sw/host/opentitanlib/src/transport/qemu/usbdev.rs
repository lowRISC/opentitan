// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::rc::Rc;

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::io::uart::Uart;

/// Pin-like interface for resetting QEMU.
///
/// QEMU can be reset over the monitor interface, however opentitanlib expects
/// to be able to assert a pin to reset the target. This type mimics a pin but
/// translates asserting it to monitor commands.
pub struct QemuVbusSense {
    pub usbdev: Rc<dyn Uart>,
    pub asserted: Cell<bool>,
}

impl QemuVbusSense {
    pub fn new(usbdev: Rc<dyn Uart>) -> QemuVbusSense {
        QemuVbusSense {
            usbdev,
            asserted: Cell::new(false),
        }
    }
}

impl GpioPin for QemuVbusSense {
    fn read(&self) -> anyhow::Result<bool> {
        log::info!("read VBUS -> {}", self.asserted.get());
        Ok(self.asserted.get())
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        log::info!("write VBUS -> {}", value);
        if value == self.asserted.get() {
            return Ok(());
        }

        let cmd = if value { "vbus_on\n" } else { "vbus_off\n" };
        self.usbdev.write(cmd.as_bytes())?;

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
