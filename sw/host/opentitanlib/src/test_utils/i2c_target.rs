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
    pub fn new(content: &[u8]) -> Self {
        let mut a = arrayvec::ArrayVec::<u8, 256>::new();
        a.try_extend_from_slice(content)
            .expect("fewer than 256 bytes");
        Self {
            length: a.len() as u8,
            address: 0,
            continuation: 0,
            data: a,
        }
    }

    pub fn execute_read<F>(&self, uart: &dyn Uart, f: F) -> Result<I2cRxResult>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::I2cReadTransaction.send(uart)?;
        self.send(uart)?;
        f()?;
        I2cRxResult::recv(uart, Duration::from_secs(300), false)
    }

    pub fn execute_write<F>(uart: &dyn Uart, command: TestCommand, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        command.send(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }
}
