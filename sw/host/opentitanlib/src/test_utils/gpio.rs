// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{UartRecv, UartSend};
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
}

impl GpioGet {
    pub fn read_all(uart: &dyn Uart) -> Result<u32> {
        TestCommand::GpioGet.send(uart)?;
        let data = GpioGet::recv(uart, Duration::from_secs(300), false)?;
        Ok(data.state)
    }
}
