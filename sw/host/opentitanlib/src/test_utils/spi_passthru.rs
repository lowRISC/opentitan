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
include!(env!("spi_passthru"));

impl ConfigJedecId {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiConfigureJedecId.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl StatusRegister {
    pub fn read(uart: &dyn Uart) -> Result<Self> {
        TestCommand::SpiReadStatus.send_with_crc(uart)?;
        Self::recv(uart, Duration::from_secs(300), false)
    }

    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiWriteStatus.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SfdpData {
    pub fn write(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiWriteSfdp.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl UploadInfo {
    pub fn execute<F>(uart: &dyn Uart, f: F) -> Result<Self>
    where
        F: FnOnce() -> Result<()>,
    {
        TestCommand::SpiWaitForUpload.send_with_crc(uart)?;
        f()?;
        Self::recv(uart, Duration::from_secs(300), false)
    }
}

impl SpiFlashReadId {
    pub fn execute(uart: &dyn Uart) -> Result<Self> {
        TestCommand::SpiFlashReadId.send_with_crc(uart)?;
        let data = SpiFlashReadId::recv(uart, Duration::from_secs(300), false)?;
        Ok(data)
    }
}

impl SpiFlashReadSfdp {
    pub fn execute(&self, uart: &dyn Uart) -> Result<SfdpData> {
        TestCommand::SpiFlashReadSfdp.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        let sfdp = SfdpData::recv(uart, Duration::from_secs(300), false)?;
        Ok(sfdp)
    }
}

impl SpiFlashEraseSector {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiFlashEraseSector.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiFlashWrite {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiFlashWrite.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiPassthruSwapMap {
    pub fn apply_address_swap(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiPassthruSetAddressMap.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiMailboxMap {
    pub fn apply(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxMap.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }

    pub fn disable(uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxUnmap.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl SpiMailboxWrite {
    pub fn execute(&self, uart: &dyn Uart) -> Result<()> {
        TestCommand::SpiMailboxWrite.send_with_crc(uart)?;
        self.send_with_crc(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}
