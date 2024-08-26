// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
include!(env!("gpio"));

impl GpioSet {
    fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::GpioSet.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }

    pub fn write(uart: &dyn Uart, pin: u32, state: bool) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::Write,
            pin_mask: pin,
            state: state.into(),
        };
        payload.execute(uart)
    }
    pub fn set_enabled(uart: &dyn Uart, pin: u32, state: bool) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::SetEnabled,
            pin_mask: pin,
            state: state.into(),
        };
        payload.execute(uart)
    }

    pub fn write_all(uart: &dyn Uart, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::WriteAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_enabled_all(uart: &dyn Uart, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::SetEnabledAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }

    pub fn write_masked(uart: &dyn Uart, mask: u32, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::WriteMasked,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_enabled_masked(uart: &dyn Uart, mask: u32, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::SetEnabledMasked,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_input_noise_filter(uart: &dyn Uart, mask: u32, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::SetInputNoiseFilter,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_restore_all(uart: &dyn Uart, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::IrqRestoreAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_disable_all(uart: &dyn Uart, state: u32) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::IrqDisableAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_acknowledge_all(uart: &dyn Uart) -> Result<()> {
        let payload = GpioSet {
            action: GpioAction::IrqAcknowledgeAll,
            pin_mask: 0,
            state: 0,
        };
        payload.execute(uart)
    }
    pub fn irq_set_trigger(uart: &dyn Uart, state: u32, trigger: String) -> Result<()> {
        match trigger.as_str() {
            "rising" => {
                let payload = GpioSet {
                    action: GpioAction::IrqSetTriggerRisingEdge,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "falling" => {
                let payload = GpioSet {
                    action: GpioAction::IrqSetTriggerFallingEdge,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "high" => {
                let payload = GpioSet {
                    action: GpioAction::IrqSetTriggerHigh,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "low" => {
                let payload = GpioSet {
                    action: GpioAction::IrqSetTriggerLow,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            _ => {
                log::error!("unsupport trigger: {:?}", trigger);
                Ok(())
            }
        }
    }
}

impl GpioGet {
    pub fn read_all(uart: &dyn Uart) -> Result<u32> {
        TestCommand::GpioGet.send(uart)?;
        let data = GpioGet::recv(uart, Duration::from_secs(300), false)?;
        Ok(data.state)
    }
}
