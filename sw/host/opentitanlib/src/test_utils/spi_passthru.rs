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
include!(env!("spi_passthru"));

impl ConfigJedecId {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiConfigureJedecId.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl StatusRegister {
    pub fn read(uart: &dyn Uart) -> Result<Self> {
        TestCommand::SpiReadStatus.send(uart)?;
        Self::recv(uart, Duration::from_secs(300), false)
    }

    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiWriteStatus.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SfdpData {
    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiWriteSfdp.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl UploadInfo {
    pub fn execute<F>(uart: &dyn Uart, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::SpiWaitForUpload.send(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }
}

impl SpiFlashReadId {
    pub fn execute(uart: &dyn Uart) -> Result<Self> {
        TestCommand::SpiFlashReadId.send(uart)?;
        let data = SpiFlashReadId::recv(uart, Duration::from_secs(300), false)?;
        Ok(data)
    }
}

impl SpiFlashReadSfdp {
    pub fn execute(&self, uart: &dyn Uart) -> Result<SfdpData> {
        TestCommand::SpiFlashReadSfdp.send(uart)?;
        self.send(uart)?;
        let sfdp = SfdpData::recv(uart, Duration::from_secs(300), false)?;
        Ok(sfdp)
    }
}

impl SpiFlashEraseSector {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiFlashEraseSector.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiFlashWrite {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiFlashWrite.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiPassthruSwapMap {
    pub fn apply_address_swap(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiPassthruSetAddressMap.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiMailboxMap {
    pub fn apply(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxMap.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }

    pub fn disable(uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxUnmap.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiMailboxWrite {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxWrite.send(uart)?;
        self.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}
