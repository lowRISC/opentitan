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
include!(env!("sysrst_ctrl"));

impl SysrstCtrlPin {
    pub fn read(&self, uart: &dyn Uart) -> Result<bool> {
        TestCommand::SysrstCtrlCommand.send(uart)?;
        SysrstCtrlCommand::ReadPin.send(uart)?;
        self.send(uart)?;
        bool::recv(uart, Duration::from_secs(300), false)
    }

    pub fn configure_override(
        &self,
        uart: &dyn Uart,
        enabled: bool,
        allow_zero: bool,
        allow_one: bool,
        override_value: bool,
    ) -> Result<()> {
        TestCommand::SysrstCtrlCommand.send(uart)?;
        SysrstCtrlCommand::ConfigurePinOverride.send(uart)?;
        let config = SysrstCtrlPinConfig {
            pin: self.clone(),
            enabled,
            allow_zero,
            allow_one,
            override_value,
        };
        config.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}
