// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::eeprom::{AddressMode, Transaction, MODE_111};
use crate::io::spi::Target;
use crate::spiflash::sfdp::{BlockEraseSize, Sfdp, SupportedAddressModes};
use anyhow::{ensure, Result};
use std::convert::TryFrom;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("address out of bounds: {0} >= {1}")]
    AddressOutOfBounds(u32, u32),
    #[error("erase at address {0} not aligned on {1}-byte boundary")]
    BadEraseAddress(u32, u32),
    #[error("erase length {0} not a multiple of {1} bytes")]
    BadEraseLength(u32, u32),
    #[error("bad sequence length: {0}")]
    BadSequenceLength(usize),
}

impl From<SupportedAddressModes> for AddressMode {
    fn from(mode: SupportedAddressModes) -> Self {
        match mode {
            SupportedAddressModes::Mode4b => AddressMode::Mode4b,
            _ => AddressMode::Mode3b,
        }
    }
}

pub struct SpiFlash {
    pub size: u32,
    pub erase_size: u32,
    pub erase_opcode: u8,
    pub program_size: u32,
    pub address_mode: AddressMode,
    pub sfdp: Option<Sfdp>,
}

impl Default for SpiFlash {
    fn default() -> Self {
        SpiFlash {
            size: 16 * 1024 * 1024,
            erase_size: 4 * 1024,
            erase_opcode: 0x20,
            program_size: SpiFlash::LEGACY_PAGE_SIZE,
            address_mode: AddressMode::default(),
            sfdp: None,
        }
    }
}

impl SpiFlash {
    // Well known SPI Flash opcodes.
    pub const READ: u8 = 0x03;
    pub const PAGE_PROGRAM: u8 = 0x02;
    pub const SECTOR_ERASE: u8 = 0x20;
    pub const CHIP_ERASE: u8 = 0xc7;
    pub const WRITE_ENABLE: u8 = 0x06;
    pub const WRITE_DISABLE: u8 = 0x04;
    pub const READ_STATUS: u8 = 0x05;
    // Winbond parts use 0x35 and 0x15 for extended status reads.
    pub const READ_STATUS2: u8 = 0x35;
    pub const READ_STATUS3: u8 = 0x15;
    pub const WRITE_STATUS: u8 = 0x01;
    // Winbond parts use 0x31 and 0x11 for extended status writes.
    pub const WRITE_STATUS2: u8 = 0x31;
    pub const WRITE_STATUS3: u8 = 0x11;
    pub const READ_ID: u8 = 0x9f;
    pub const ENTER_4B: u8 = 0xb7;
    pub const EXIT_4B: u8 = 0xe9;
    pub const READ_SFDP: u8 = 0x5a;
    pub const NOP: u8 = 0x00;
    pub const RESET_ENABLE: u8 = 0x66;
    pub const RESET: u8 = 0x99;

    /// The legacy JEDEC page size for programming operations is 256 bytes.
    pub const LEGACY_PAGE_SIZE: u32 = 256;

    /// Status register bits:
    /// The `WIP` bit indicates a write in progress (sometimes called the busy bit).
    pub const STATUS_WIP: u8 = 0x01;
    /// The `WEL` bit is the write enable latch.
    pub const STATUS_WEL: u8 = 0x02;

    /// Read `length` bytes of the JEDEC ID from the `spi` target.
    pub fn read_jedec_id(spi: &dyn Target, length: usize) -> Result<Vec<u8>> {
        let mut buf = vec![0u8; length];
        spi.run_eeprom_transactions(&mut [Transaction::Read(
            MODE_111.cmd(SpiFlash::READ_ID),
            &mut buf,
        )])?;
        Ok(buf)
    }

    /// Read status register from the `spi` target.
    pub fn read_status(spi: &dyn Target) -> Result<u8> {
        let mut buf = [0u8; 1];
        spi.run_eeprom_transactions(&mut [Transaction::Read(
            MODE_111.cmd(SpiFlash::READ_STATUS),
            &mut buf,
        )])?;
        Ok(buf[0])
    }

    /// Read the extended status register from the `spi` target.
    pub fn read_status_ex(spi: &dyn Target, seq: Option<&[u8]>) -> Result<u32> {
        let seq = seq.unwrap_or(&[Self::READ_STATUS, Self::READ_STATUS2, Self::READ_STATUS3]);
        ensure!(
            seq.len() > 0 && seq.len() <= 3,
            Error::BadSequenceLength(seq.len())
        );
        let mut buf = [0u8; 4];
        for (op, byte) in seq.iter().zip(buf.iter_mut()) {
            spi.run_eeprom_transactions(&mut [Transaction::Read(
                MODE_111.cmd(*op),
                std::slice::from_mut(byte),
            )])?;
        }
        Ok(u32::from_le_bytes(buf))
    }

    /// Poll the status register waiting for the busy bit to clear.
    pub fn wait_for_busy_clear(spi: &dyn Target) -> Result<()> {
        spi.run_eeprom_transactions(&mut [Transaction::WaitForBusyClear])?;
        Ok(())
    }

    /// Send the WRITE_ENABLE opcode to the `spi` target.
    pub fn set_write_enable(spi: &dyn Target) -> Result<()> {
        spi.run_eeprom_transactions(&mut [Transaction::Command(
            MODE_111.cmd(SpiFlash::WRITE_ENABLE),
        )])?;
        Ok(())
    }

    /// Send the WRITE_DISABLE opcode to the `spi` target.
    pub fn set_write_disable(spi: &dyn Target) -> Result<()> {
        spi.run_eeprom_transactions(&mut [Transaction::Command(
            MODE_111.cmd(SpiFlash::WRITE_DISABLE),
        )])?;
        Ok(())
    }

    /// Read and parse the SFDP table from the `spi` target.
    pub fn read_sfdp(spi: &dyn Target) -> Result<Sfdp> {
        let mut buf = vec![0u8; 256];
        let mut tries = 0;
        loop {
            // READ_SFDP always takes a 3-byte address followed by a dummy byte regardless of
            // address mode.
            spi.run_eeprom_transactions(&mut [Transaction::Read(
                MODE_111
                    .dummy_cycles(8)
                    .cmd_addr(SpiFlash::READ_SFDP, 0, AddressMode::Mode3b),
                &mut buf,
            )])?;

            // We only want to give SFDP parsing one extra chance for length
            // extension. If parsing fails a second time, just return the error.
            let result = Sfdp::try_from(&buf[..]);
            if result.is_ok() || tries > 0 {
                return result;
            }
            buf.resize(Sfdp::length_required(&buf)?, 0);
            tries += 1;
        }
    }

    /// Create a new `SpiFlash` instance from an SFDP table.
    pub fn from_sfdp(sfdp: Sfdp) -> Self {
        let (erase_sz, erase_op) = match sfdp.jedec.block_erase_size {
            BlockEraseSize::Block4KiB => (4096, sfdp.jedec.erase_opcode_4kib),
            _ => (sfdp.jedec.erase[0].size, sfdp.jedec.erase[0].opcode),
        };
        SpiFlash {
            size: sfdp.jedec.density,
            erase_size: erase_sz,
            erase_opcode: erase_op,
            program_size: SpiFlash::LEGACY_PAGE_SIZE,
            address_mode: AddressMode::from(sfdp.jedec.address_modes),
            sfdp: Some(sfdp),
        }
    }

    /// Create a new `SpiFlash` instance by reading an SFDP table from the `spi` Target.
    pub fn from_spi(spi: &dyn Target) -> Result<Self> {
        let sfdp = SpiFlash::read_sfdp(spi)?;
        Ok(SpiFlash::from_sfdp(sfdp))
    }

    /// Set the SPI flash addressing mode to either 3b or 4b mode.
    pub fn set_address_mode(&mut self, spi: &dyn Target, mode: AddressMode) -> Result<()> {
        let opcode = match mode {
            AddressMode::Mode3b => SpiFlash::EXIT_4B,
            AddressMode::Mode4b => SpiFlash::ENTER_4B,
        };
        spi.run_eeprom_transactions(&mut [Transaction::Command(MODE_111.cmd(opcode))])?;
        self.address_mode = mode;
        Ok(())
    }

    /// Automatically set the addressing mode based on the size of the SPI flash.
    pub fn set_address_mode_auto(&mut self, spi: &dyn Target) -> Result<()> {
        self.set_address_mode(
            spi,
            if self.size <= 16 * 1024 * 1024 {
                AddressMode::Mode3b
            } else {
                AddressMode::Mode4b
            },
        )
    }

    /// Read into `buffer` from the SPI flash starting at `address`.
    pub fn read(&self, spi: &dyn Target, address: u32, buffer: &mut [u8]) -> Result<&Self> {
        self.read_with_progress(spi, address, buffer, |_, _| {})
    }

    /// Read into `buffer` from the SPI flash starting at `address`.
    /// The `progress` callback will be invoked after each chunk of the read operation.
    pub fn read_with_progress(
        &self,
        spi: &dyn Target,
        mut address: u32,
        buffer: &mut [u8],
        progress: impl Fn(u32, u32),
    ) -> Result<&Self> {
        // Break the read up according to the maximum chunksize the backend can handle.
        for chunk in buffer.chunks_mut(spi.max_chunk_size()?) {
            spi.run_eeprom_transactions(&mut [Transaction::Read(
                MODE_111.cmd_addr(SpiFlash::READ, address, self.address_mode),
                chunk,
            )])?;
            address += chunk.len() as u32;
            progress(address, chunk.len() as u32);
        }
        Ok(self)
    }

    /// Erase the entire EEPROM via the CHIP_ERASE opcode.
    pub fn chip_erase(&self, spi: &dyn Target) -> Result<&Self> {
        spi.run_eeprom_transactions(&mut [
            Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
            Transaction::Command(MODE_111.cmd(SpiFlash::CHIP_ERASE)),
            Transaction::WaitForBusyClear,
        ])?;
        Ok(self)
    }

    /// Erase a segment of the SPI flash starting at `address` for `length` bytes.
    /// The address and length must be sector aligned.
    pub fn erase(&self, spi: &dyn Target, address: u32, length: u32) -> Result<&Self> {
        self.erase_with_progress(spi, address, length, |_, _| {})
    }

    /// Erase a segment of the SPI flash starting at `address` for `length` bytes.
    /// The address and length must be sector aligned.
    /// The `progress` callback will be invoked after each chunk of the erase operation.
    pub fn erase_with_progress(
        &self,
        spi: &dyn Target,
        address: u32,
        length: u32,
        progress: impl Fn(u32, u32),
    ) -> Result<&Self> {
        if address % self.erase_size != 0 {
            return Err(Error::BadEraseAddress(address, self.erase_size).into());
        }
        if length % self.erase_size != 0 {
            return Err(Error::BadEraseLength(length, self.erase_size).into());
        }
        let end = address + length;
        for addr in (address..end).step_by(self.erase_size as usize) {
            spi.run_eeprom_transactions(&mut [
                Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
                Transaction::Command(MODE_111.cmd_addr(
                    SpiFlash::SECTOR_ERASE,
                    addr,
                    self.address_mode,
                )),
                Transaction::WaitForBusyClear,
            ])?;
            progress(addr, self.erase_size);
        }
        Ok(self)
    }

    /// Program a segment of the SPI flash starting at `address` with the contents of `buffer`.
    /// The address and buffer length may be arbitrary.  This function will not
    /// erase the segment first.
    pub fn program(&self, spi: &dyn Target, address: u32, buffer: &[u8]) -> Result<&Self> {
        self.program_with_progress(spi, address, buffer, |_, _| {})
    }

    /// Program a segment of the SPI flash starting at `address` with the contents of `buffer`.
    /// The address and buffer length may be arbitrary.  This function will not
    /// erase the segment first.
    /// The `progress` callback will be invoked after each chunk of the program operation.
    pub fn program_with_progress(
        &self,
        spi: &dyn Target,
        mut address: u32,
        buffer: &[u8],
        progress: impl Fn(u32, u32),
    ) -> Result<&Self> {
        let mut remain = buffer.len();
        let mut chunk_start = 0usize;
        while remain != 0 {
            // If the address isn't program-page-size aligned, adjust the first
            // chunk so that subsequent writes will be so-aligned.
            // This is necessary because the SPI eeprom will wrap within the
            // programming page and the resultant data in the eeprom will not
            // be what you intended.
            let chunk_size = (self.program_size - (address % self.program_size)) as usize;
            let chunk_size = std::cmp::min(chunk_size, remain);
            let chunk_end = chunk_start + chunk_size;
            let chunk = &buffer[chunk_start..chunk_end];
            // Skip this chunk if all bytes are 0xff.
            if !chunk.iter().all(|&x| x == 0xff) {
                spi.run_eeprom_transactions(&mut [
                    Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
                    Transaction::Write(
                        MODE_111.cmd_addr(SpiFlash::PAGE_PROGRAM, address, self.address_mode),
                        chunk,
                    ),
                    Transaction::WaitForBusyClear,
                ])?;
            }
            address += chunk_size as u32;
            chunk_start += chunk_size;
            remain -= chunk_size;
            progress(address, chunk_size as u32);
        }
        Ok(self)
    }

    /// Send the software reset sequence to the `spi` target.
    pub fn chip_reset(spi: &dyn Target) -> Result<()> {
        spi.run_eeprom_transactions(&mut [
            Transaction::Command(MODE_111.cmd(SpiFlash::RESET_ENABLE)),
            Transaction::Command(MODE_111.cmd(SpiFlash::RESET)),
        ])?;
        Ok(())
    }
}
