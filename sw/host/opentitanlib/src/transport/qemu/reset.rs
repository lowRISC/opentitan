// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::transport::qemu::monitor::{Monitor, QomPropertyValue};

/// Pin-like interface for resetting QEMU.
///
/// QEMU can be reset over the monitor interface, however opentitanlib expects
/// to be able to assert a pin to reset the target. This type mimics a pin but
/// translates asserting it to monitor commands.
pub struct QemuReset {
    pub monitor: Rc<RefCell<Monitor>>,
    pub asserted: Cell<bool>,
}

impl QemuReset {
    pub fn new(monitor: Rc<RefCell<Monitor>>) -> QemuReset {
        QemuReset {
            monitor,
            asserted: Cell::new(false),
        }
    }
}

impl GpioPin for QemuReset {
    fn read(&self) -> anyhow::Result<bool> {
        Ok(self.asserted.get())
    }

    fn write(&self, value: bool) -> anyhow::Result<()> {
        if value == self.asserted.get() {
            return Ok(());
        }

        let mut monitor = self.monitor.borrow_mut();

        match value {
            false => {
                monitor.stop()?;
                monitor.set_property(
                    Some("ot-eg-pad-ring.0"),
                    "por_n",
                    &QomPropertyValue::String("low".to_string()),
                )?;
                monitor.reset()?;
            }
            true => {
                monitor.set_property(
                    Some("ot-eg-pad-ring.0"),
                    "por_n",
                    &QomPropertyValue::String("high".to_string()),
                )?;
                monitor.cont()?;
            }
        }

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
