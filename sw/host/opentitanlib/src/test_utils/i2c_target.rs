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
include!(env!("i2c_target"));

impl I2cTargetAddress {
    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::I2cTargetAddress.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl I2cTransferStart {
    pub fn new(address: u8, content: &[u8], stop: bool) -> Self {
        let mut a = arrayvec::ArrayVec::<u8, 256>::new();
        a.try_extend_from_slice(content)
            .expect("fewer than 256 bytes");
        Self {
            length: a.len() as u8,
            address,
            stop,
            data: a,
        }
    }

    pub fn execute_read<F>(&self, uart: &dyn Uart, f: F) -> Result<()>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::I2cStartTransferRead.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        f()?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }

    pub fn execute_write<F>(uart: &dyn Uart, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::I2cStartTransferWrite.send_with_crc(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }

    pub fn execute_write_slow<F>(uart: &dyn Uart, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::I2cStartTransferWriteSlow.send_with_crc(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }

    pub fn execute_write_read<F>(&self, uart: &dyn Uart, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::I2cStartTransferWriteRead.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }
}

impl I2cTestConfig {
    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::I2cTestConfig.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}
