// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use ot_hal::top::earlgrey::{PinmuxOutsel, PinmuxPeripheralIn};

use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
include!(env!("gpio"));

/// Number of pins of each GPIO instance.
pub const GPIO_PINS: u32 = 32;

/// Pinmux peripheral input and output select of pin 0 of each GPIO instance.
pub static GPIO_INSTANCES: [(PinmuxPeripheralIn, PinmuxOutsel); 2] = [
    (PinmuxPeripheralIn::Gpio0Gpio0, PinmuxOutsel::Gpio0Gpio0),
    (PinmuxPeripheralIn::Gpio1Gpio0, PinmuxOutsel::Gpio1Gpio0),
];

/// Returns the pinmux peripheral input of a pin of a GPIO instance.
pub fn peripheral_in(instance: u8, pin: u32) -> PinmuxPeripheralIn {
    assert!(pin < GPIO_PINS, "GPIO pin {pin} out of range");
    let (base, _) = GPIO_INSTANCES[usize::from(instance)];
    PinmuxPeripheralIn(u32::from(base) + pin)
}

/// Returns the pinmux output select of a pin of a GPIO instance.
pub fn outsel(instance: u8, pin: u32) -> PinmuxOutsel {
    assert!(pin < GPIO_PINS, "GPIO pin {pin} out of range");
    let (_, base) = GPIO_INSTANCES[usize::from(instance)];
    PinmuxOutsel(u32::from(base) + pin)
}

/// Returns the pin index of a GPIO peripheral input within its GPIO instance.
pub fn input_pin(input: PinmuxPeripheralIn) -> u32 {
    GPIO_INSTANCES
        .iter()
        .map(|(base, _)| u32::from(input).wrapping_sub(u32::from(*base)))
        .find(|i| *i < GPIO_PINS)
        .expect("not a GPIO peripheral input")
}

/// Returns the pin index of a GPIO output select within its GPIO instance.
pub fn output_pin(output: PinmuxOutsel) -> u32 {
    GPIO_INSTANCES
        .iter()
        .map(|(_, base)| u32::from(output).wrapping_sub(u32::from(*base)))
        .find(|i| *i < GPIO_PINS)
        .expect("not a GPIO output select")
}

impl GpioSet {
    fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::GpioSet.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false, false)?;
        Ok(())
    }

    pub fn write(uart: &dyn Uart, instance: u8, pin: u32, state: bool) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::Write,
            pin_mask: pin,
            state: state.into(),
        };
        payload.execute(uart)
    }
    pub fn set_enabled(uart: &dyn Uart, instance: u8, pin: u32, state: bool) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::SetEnabled,
            pin_mask: pin,
            state: state.into(),
        };
        payload.execute(uart)
    }

    pub fn write_all(uart: &dyn Uart, instance: u8, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::WriteAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_enabled_all(uart: &dyn Uart, instance: u8, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::SetEnabledAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }

    pub fn write_masked(uart: &dyn Uart, instance: u8, mask: u32, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::WriteMasked,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_enabled_masked(uart: &dyn Uart, instance: u8, mask: u32, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::SetEnabledMasked,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn set_input_noise_filter(
        uart: &dyn Uart,
        instance: u8,
        mask: u32,
        state: u32,
    ) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::SetInputNoiseFilter,
            pin_mask: mask,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_restore_all(uart: &dyn Uart, instance: u8, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::IrqRestoreAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_disable_all(uart: &dyn Uart, instance: u8, state: u32) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::IrqDisableAll,
            pin_mask: 0,
            state,
        };
        payload.execute(uart)
    }
    pub fn irq_acknowledge_all(uart: &dyn Uart, instance: u8) -> Result<()> {
        let payload = GpioSet {
            instance,
            action: GpioAction::IrqAcknowledgeAll,
            pin_mask: 0,
            state: 0,
        };
        payload.execute(uart)
    }
    pub fn irq_set_trigger(
        uart: &dyn Uart,
        instance: u8,
        state: u32,
        trigger: String,
    ) -> Result<()> {
        match trigger.as_str() {
            "rising" => {
                let payload = GpioSet {
                    instance,
                    action: GpioAction::IrqSetTriggerRisingEdge,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "falling" => {
                let payload = GpioSet {
                    instance,
                    action: GpioAction::IrqSetTriggerFallingEdge,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "high" => {
                let payload = GpioSet {
                    instance,
                    action: GpioAction::IrqSetTriggerHigh,
                    pin_mask: 0,
                    state,
                };
                payload.execute(uart)
            }
            "low" => {
                let payload = GpioSet {
                    instance,
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
    pub fn read_all(uart: &dyn Uart, instance: u8) -> Result<u32> {
        TestCommand::GpioGet.send(uart)?;
        GpioGetRequest { instance }.send(uart)?;
        let data = GpioGet::recv(uart, Duration::from_secs(300), false, false)?;
        Ok(data.state)
    }
}
