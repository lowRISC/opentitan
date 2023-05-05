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
include!(env!("i2c_target"));

impl I2cTargetAddress {
    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::I2cTargetAddress.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl I2cTransaction {
    pub fn read(uart: &dyn Uart) -> Result<Self> {
        TestCommand::I2cReadTransaction.send(uart)?;
        Self::recv(uart, Duration::from_secs(300), false)
    }

    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::I2cWriteTransaction.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}
