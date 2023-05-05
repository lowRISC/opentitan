// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::app::NoProgressBar;
use crate::io::eeprom::{AddressMode, Mode, Transaction, MODE_111, MODE_112, MODE_114};
use crate::io::spi::Target;
use crate::spiflash::sfdp::{
    BlockEraseSize, FastReadParam, SectorErase, Sfdp, SupportedAddressModes,
};
use crate::transport::ProgressIndicator;
use anyhow::{ensure, Result};
use std::convert::TryFrom;
use structopt::clap::arg_enum;
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
    #[error("unsupported mode: {0:?}")]
    UnsupportedMode(ReadMode),
}

impl From<SupportedAddressModes> for AddressMode {
    fn from(mode: SupportedAddressModes) -> Self {
        match mode {
            SupportedAddressModes::Mode4b => AddressMode::Mode4b,
            _ => AddressMode::Mode3b,
        }
    }
}

arg_enum! {
#[derive(Debug, Clone, Copy)]
pub enum ReadMode {
    Standard,
    Fast,
    Dual,
    Quad,
}
}

// Conflict between deriving Default and the `arg_enum!` macro.
// The workaround is to manually derive Default.
#[allow(clippy::derivable_impls)]
impl Default for ReadMode {
    fn default() -> Self {
        ReadMode::Standard
    }
}

pub struct ReadTypes {
    pub standard: FastReadParam,
    pub fast: FastReadParam,
    pub dual: FastReadParam,
    pub quad: FastReadParam,
}

impl Default for ReadTypes {
    fn default() -> Self {
        Self {
            standard: FastReadParam {
                wait_states: 0,
                mode_bits: 0,
                opcode: SpiFlash::READ,
            },
            fast: FastReadParam {
                wait_states: 8,
                mode_bits: 0,
                opcode: SpiFlash::FAST_READ,
            },
            dual: FastReadParam {
                wait_states: 8,
                mode_bits: 0,
                opcode: SpiFlash::FAST_DUAL_READ,
            },
            quad: FastReadParam {
                wait_states: 8,
                mode_bits: 0,
                opcode: SpiFlash::FAST_QUAD_READ,
            },
        }
    }
}

impl ReadTypes {
    pub fn from_sfdp(sfdp: &Sfdp) -> Self {
        Self {
            standard: FastReadParam {
                wait_states: 0,
                mode_bits: 0,
                opcode: SpiFlash::READ,
            },
            fast: FastReadParam {
                wait_states: 8,
                mode_bits: 0,
                opcode: SpiFlash::FAST_READ,
            },
            dual: if sfdp.jedec.support_fast_read_112 {
                sfdp.jedec.param_112.clone()
            } else {
                Default::default()
            },
            quad: if sfdp.jedec.support_fast_read_114 {
                sfdp.jedec.param_114.clone()
            } else {
                Default::default()
            },
        }
    }
}

arg_enum! {
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EraseMode {
    Standard,
    Block,
}
}

// Conflict between deriving Default and the `arg_enum!` macro.
// The workaround is to manually derive Default.
#[allow(clippy::derivable_impls)]
impl Default for EraseMode {
    fn default() -> Self {
        EraseMode::Standard
    }
}

pub struct SpiFlash {
    pub size: u32,
    pub program_size: u32,
    pub address_mode: AddressMode,
    pub read_mode: ReadMode,
    pub erase_mode: EraseMode,
    pub sfdp: Option<Sfdp>,
    pub read_type: ReadTypes,
    pub erase: Vec<SectorErase>,
}

impl Default for SpiFlash {
    fn default() -> Self {
        SpiFlash {
            size: 16 * 1024 * 1024,
            program_size: SpiFlash::LEGACY_PAGE_SIZE,
            address_mode: Default::default(),
            read_mode: Default::default(),
            erase_mode: Default::default(),
            sfdp: None,
            read_type: Default::default(),
            erase: vec![SectorErase {
                size: 4096,
                opcode: SpiFlash::SECTOR_ERASE,
                time: None,
            }],
        }
    }
}

impl SpiFlash {
    // Well known SPI Flash opcodes.
    pub const READ: u8 = 0x03;
    pub const FAST_READ: u8 = 0x0b;
    pub const FAST_DUAL_READ: u8 = 0x3b;
    pub const FAST_QUAD_READ: u8 = 0x6b;
    pub const PAGE_PROGRAM: u8 = 0x02;
    pub const SECTOR_ERASE: u8 = 0x20;
    pub const BLOCK_ERASE_32K: u8 = 0x52;
    pub const BLOCK_ERASE_64K: u8 = 0xD8;
    pub const SECTOR_ERASE_4B: u8 = 0x21;
    pub const BLOCK_ERASE_32K_4B: u8 = 0x5C;
    pub const BLOCK_ERASE_64K_4B: u8 = 0xDC;
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
            !seq.is_empty() && seq.len() <= 3,
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
            let mut eeprom_transactions = Vec::new();
            let read_size = spi.get_eeprom_max_transfer_sizes()?.read;
            for (i, transfer) in buf.chunks_mut(read_size).enumerate() {
                eeprom_transactions.push(Transaction::Read(
                    MODE_111.dummy_cycles(8).cmd_addr(
                        SpiFlash::READ_SFDP,
                        (i * read_size) as u32,
                        AddressMode::Mode3b,
                    ),
                    transfer,
                ));
            }
            spi.run_eeprom_transactions(&mut eeprom_transactions)?;

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
        let read_type = ReadTypes::from_sfdp(&sfdp);
        let mut erase = sfdp
            .jedec
            .erase
            .iter()
            .filter_map(|e| if e.size != 0 { Some(e.clone()) } else { None })
            .collect::<Vec<_>>();
        // If the SFDP claims to support 4K erases, but a 4K SectorErase is not
        // present, synthesize one and add it to the list.
        if sfdp.jedec.block_erase_size == BlockEraseSize::Block4KiB
            && !erase.iter().any(|e| e.size == 4096)
        {
            erase.push(SectorErase {
                size: 4096,
                opcode: sfdp.jedec.erase_opcode_4kib,
                time: None,
            });
        }
        // Sort largest to smallest.
        erase.sort_by(|a, b| b.size.cmp(&a.size));

        SpiFlash {
            size: sfdp.jedec.density,
            program_size: SpiFlash::LEGACY_PAGE_SIZE,
            address_mode: AddressMode::from(sfdp.jedec.address_modes),
            read_mode: Default::default(),
            erase_mode: Default::default(),
            sfdp: Some(sfdp),
            read_type,
            erase,
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
        self.read_with_progress(spi, address, buffer, &NoProgressBar)
    }

    fn select_read(&self) -> Result<(Mode, &FastReadParam)> {
        match self.read_mode {
            ReadMode::Standard => Ok((MODE_111, &self.read_type.standard)),
            ReadMode::Fast => Ok((MODE_111, &self.read_type.fast)),
            ReadMode::Dual if self.read_type.dual.opcode != 0 => {
                Ok((MODE_112, &self.read_type.dual))
            }
            ReadMode::Quad if self.read_type.quad.opcode != 0 => {
                Ok((MODE_114, &self.read_type.quad))
            }
            _ => Err(Error::UnsupportedMode(self.read_mode).into()),
        }
    }

    /// Read into `buffer` from the SPI flash starting at `address`.
    /// The `progress` callback will be invoked after each chunk of the read operation.
    pub fn read_with_progress(
        &self,
        spi: &dyn Target,
        mut address: u32,
        buffer: &mut [u8],
        progress: &dyn ProgressIndicator,
    ) -> Result<&Self> {
        progress.new_stage("", buffer.len());
        let (mode, param) = self.select_read()?;
        // Break the read up according to the maximum chunksize the backend can handle.
        let chunk_size = spi.get_eeprom_max_transfer_sizes()?.read;
        for (idx, chunk) in buffer.chunks_mut(chunk_size).enumerate() {
            progress.progress(idx * chunk_size);
            spi.run_eeprom_transactions(&mut [Transaction::Read(
                mode.dummy_cycles(param.wait_states).cmd_addr(
                    param.opcode,
                    address,
                    self.address_mode,
                ),
                chunk,
            )])?;
            address += chunk.len() as u32;
        }
        progress.progress(buffer.len());
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
        self.erase_with_progress(spi, address, length, &NoProgressBar)
    }

    fn select_erase(&self, address: u32, length: u32) -> Result<&SectorErase> {
        if self.erase_mode == EraseMode::Standard {
            // We assume the last element of the `erase` list is the standard
            // SECTOR_ERASE.  So far, this has been true for all eeproms
            // encountered by the author.
            return Ok(self.erase.last().unwrap());
        }
        for e in self.erase.iter() {
            if address % e.size == 0 && length >= e.size {
                return Ok(e);
            }
        }
        Err(Error::BadEraseAddress(address, self.erase.last().unwrap().size).into())
    }

    /// Erase a segment of the SPI flash starting at `address` for `length` bytes.
    /// The address and length must be sector aligned.
    /// The `progress` callback will be invoked after each chunk of the erase operation.
    pub fn erase_with_progress(
        &self,
        spi: &dyn Target,
        address: u32,
        length: u32,
        progress: &dyn ProgressIndicator,
    ) -> Result<&Self> {
        let min_erase_size = self.erase.last().unwrap().size;
        if address % min_erase_size != 0 {
            return Err(Error::BadEraseAddress(address, min_erase_size).into());
        }
        if length % min_erase_size != 0 {
            return Err(Error::BadEraseLength(length, min_erase_size).into());
        }
        progress.new_stage("", length as usize);
        let end = address + length;
        let mut addr = address;
        while addr < end {
            let erase = self.select_erase(addr, end - addr)?;
            spi.run_eeprom_transactions(&mut [
                Transaction::Command(MODE_111.cmd(SpiFlash::WRITE_ENABLE)),
                Transaction::Command(MODE_111.cmd_addr(erase.opcode, addr, self.address_mode)),
                Transaction::WaitForBusyClear,
            ])?;
            progress.progress((addr - address) as usize);
            addr += erase.size;
        }
        progress.progress(length as usize);
        Ok(self)
    }

    /// Program a segment of the SPI flash starting at `address` with the contents of `buffer`.
    /// The address and buffer length may be arbitrary.  This function will not
    /// erase the segment first.
    pub fn program(&self, spi: &dyn Target, address: u32, buffer: &[u8]) -> Result<&Self> {
        self.program_with_progress(spi, address, buffer, &NoProgressBar)
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
        progress: &dyn ProgressIndicator,
    ) -> Result<&Self> {
        progress.new_stage("", buffer.len());
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
            progress.progress(buffer.len() - remain);
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
