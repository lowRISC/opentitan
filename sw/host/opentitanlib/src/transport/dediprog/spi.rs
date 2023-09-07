// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::eeprom;
use crate::io::eeprom::Transaction::{Read, WaitForBusyClear, Write};
use crate::io::spi::{
    AssertChipSelect, ClockPolarity, MaxSizes, SpiError, Target, TargetChipDeassert, Transfer,
    TransferMode,
};
use crate::spiflash::flash::SpiFlash;
use crate::transport::dediprog::{ClockSpeed, Command, Inner};
use crate::util::voltage::Voltage;

pub struct DediprogSpi {
    inner: Rc<RefCell<Inner>>,
    max_chunk_size: usize,
}

#[repr(u8)]
enum ReadMode {
    ReadStandard = 1,
    ReadFast = 2,
    ReadAtmel45 = 3,
    Read4bAddrFast = 4,
    Read4bAddrFast0x0c = 5,
}

#[repr(u8)]
enum WriteMode {
    WritePageProgram = 1,
    WritePageWrite = 2,
    Write1bAai = 3,
    Write2bAai = 4,
    Write128bPage = 5,
    WritePageAt26df041 = 6,
    WriteSiliconBlueFpga = 7,
    Write64bPageNumonyx = 8,
    Write4bAddr256bPagePgm = 9,
    Write32bPageMxic512k = 10,
    Write4bAdr256bPagePgm0x12 = 11,
    Write4bAdr256bPagePgmFlags = 12,
}

impl DediprogSpi {
    const MAX_GENERIC_DATA_LEN: usize = 16;

    const READ_CHUNK_SIZE: usize = 512;
    const WRITE_CHUNK_SIZE: usize = 256;

    pub fn open(inner: Rc<RefCell<Inner>>) -> Result<Self> {
        let this = Self {
            inner,
            max_chunk_size: 65535 * 256,
        };
        this.set_spi_clock()?;
        Ok(this)
    }

    fn set_spi_clock(&self) -> Result<()> {
        self.inner.borrow().device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::SetSpiClk as u8,
            self.inner.borrow().spi_clock as u16,
            0,
            &[],
        )?;
        Ok(())
    }

    fn read_sfdp(&self, mut address: u32, mut rbuf: &mut [u8]) -> Result<()> {
        // Read 16 bytes at a time, returning a single result.
        while !rbuf.is_empty() {
            let chunk_size = std::cmp::min(rbuf.len(), Self::MAX_GENERIC_DATA_LEN);
            let addr_bytes = address.to_be_bytes();
            let sub_cmd: [u8; 5] = [
                SpiFlash::READ_SFDP,
                addr_bytes[1],
                addr_bytes[2],
                addr_bytes[3],
                0,
            ];
            self.transmit(&sub_cmd, chunk_size)?;
            self.receive(&mut rbuf[..chunk_size])?;
            rbuf = &mut rbuf[chunk_size..];
            address += chunk_size as u32;
        }
        Ok(())
    }

    fn transmit(&self, wbuf: &[u8], rbuf_len: usize) -> Result<()> {
        self.inner.borrow().device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::Transceive as u8,
            rbuf_len as u16,
            0,
            wbuf,
        )?;
        Ok(())
    }

    /// Receive data for a single SPI operation, using one or more USB packets.
    fn receive(&self, rbuf: &mut [u8]) -> Result<()> {
        self.inner.borrow().device.read_control(
            rusb::request_type(
                rusb::Direction::In,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::Transceive as u8,
            0,
            0,
            rbuf,
        )?;
        Ok(())
    }

    fn eeprom_read_transaction(&self, cmd: &eeprom::Cmd, rbuf: &mut [u8]) -> Result<()> {
        let mut usbcmd = [0u8; 10];
        match (
            cmd.get_opcode(),
            cmd.get_address_len(),
            cmd.get_dummy_cycles(),
        ) {
            ([SpiFlash::READ_SFDP], 3, 8) => {
                return self.read_sfdp(cmd.get_address(), rbuf);
            }
            ([SpiFlash::READ], 3, 0) => {
                // Standard read, 3-byte address
                usbcmd[3] = ReadMode::ReadStandard as u8;
                usbcmd[4] = SpiFlash::READ;
            }
            ([SpiFlash::READ], 4, 0) => {
                // Standard read, 4-byte address.  Dediprog may not support 4 byte address on
                // standard read, do 4b fast read instead.
                usbcmd[3] = ReadMode::Read4bAddrFast as u8;
                usbcmd[4] = SpiFlash::FAST_READ;
            }
            _ => bail!(SpiError::InvalidTransferMode(
                "Command not supported".to_string()
            )),
        }

        ensure!(
            rbuf.len() % Self::READ_CHUNK_SIZE == 0,
            SpiError::InvalidTransferMode(format!(
                "Read length {} not multiple of {}",
                rbuf.len(),
                Self::READ_CHUNK_SIZE
            ))
        );

        let chunks = (rbuf.len() / Self::READ_CHUNK_SIZE) as u16;

        usbcmd[0..2].clone_from_slice(&chunks.to_le_bytes());
        usbcmd[6..10].clone_from_slice(&cmd.get_address().to_le_bytes());
        self.inner.borrow().device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::Read as u8,
            0,
            0,
            &usbcmd,
        )?;
        for chunk in rbuf.chunks_exact_mut(Self::READ_CHUNK_SIZE) {
            self.inner
                .borrow()
                .device
                .read_bulk(self.inner.borrow().in_endpoint, chunk)?;
        }
        Ok(())
    }

    fn eeprom_write_transaction(
        &self,
        cmd: &eeprom::Cmd,
        wbuf: &[u8],
        _wait_for_busy_clear: bool,
    ) -> Result<()> {
        ensure!(
            wbuf.len() % Self::WRITE_CHUNK_SIZE == 0,
            SpiError::InvalidTransferMode(format!(
                "Write length {} not multiple of {}",
                wbuf.len(),
                Self::WRITE_CHUNK_SIZE
            ))
        );

        let chunks = (wbuf.len() / Self::WRITE_CHUNK_SIZE) as u16;

        let mut usbcmd = [0u8; 10];
        usbcmd[0..2].clone_from_slice(&chunks.to_le_bytes());

        match (
            cmd.get_opcode(),
            cmd.get_address_len(),
            cmd.get_dummy_cycles(),
        ) {
            ([SpiFlash::PAGE_PROGRAM], 3, 0) => {
                usbcmd[3] = WriteMode::WritePageProgram as u8;
                usbcmd[4] = SpiFlash::PAGE_PROGRAM;
            }
            ([SpiFlash::PAGE_PROGRAM], 4, 0) => {
                usbcmd[3] = WriteMode::Write4bAddr256bPagePgm as u8;
                usbcmd[4] = SpiFlash::PAGE_PROGRAM;
            }
            _ => bail!(SpiError::InvalidTransferMode(
                "Command not supported".to_string()
            )),
        }
        usbcmd[6..10].clone_from_slice(&cmd.get_address().to_le_bytes());
        self.inner.borrow().device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::Write as u8,
            0,
            0,
            &usbcmd,
        )?;
        for chunk in wbuf.chunks_exact(Self::WRITE_CHUNK_SIZE) {
            let mut buf = [0xFFu8; 512];
            buf[0..Self::WRITE_CHUNK_SIZE].clone_from_slice(chunk);
            self.inner
                .borrow()
                .device
                .write_bulk(self.inner.borrow().out_endpoint, &buf)?;
        }
        Ok(())
    }

    fn do_run_eeprom_transactions(
        &self,
        mut transactions: &mut [eeprom::Transaction],
    ) -> Result<()> {
        loop {
            match transactions {
                [eeprom::Transaction::Command(pre_cmd), Write(cmd, wbuf), WaitForBusyClear, rest @ ..] =>
                {
                    transactions = rest;
                    if pre_cmd.get_opcode() == [SpiFlash::WRITE_ENABLE] {
                        // Write enable is done by eeprom_write_transaction()
                    } else {
                        self.run_transaction(&mut [Transfer::Write(cmd.to_bytes()?)])?
                    }
                    self.eeprom_write_transaction(cmd, wbuf, true)?;
                }
                [eeprom::Transaction::Command(cmd), rest @ ..] => {
                    transactions = rest;
                    self.run_transaction(&mut [Transfer::Write(cmd.to_bytes()?)])?
                }
                [Read(cmd, ref mut rbuf), rest @ ..] => {
                    transactions = rest;
                    self.eeprom_read_transaction(cmd, rbuf)?;
                }
                [Write(cmd, wbuf), WaitForBusyClear, rest @ ..] => {
                    transactions = rest;
                    self.eeprom_write_transaction(cmd, wbuf, true)?;
                }
                [Write(cmd, wbuf), rest @ ..] => {
                    transactions = rest;
                    self.eeprom_write_transaction(cmd, wbuf, false)?;
                }
                [WaitForBusyClear, rest @ ..] => {
                    transactions = rest;
                    let mut status = eeprom::STATUS_WIP;
                    while status & eeprom::STATUS_WIP != 0 {
                        self.run_transaction(&mut [
                            Transfer::Write(&[eeprom::READ_STATUS]),
                            Transfer::Read(std::slice::from_mut(&mut status)),
                        ])?;
                    }
                }
                [] => return Ok(()),
            }
        }
    }
}

impl Target for DediprogSpi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        unimplemented!();
    }
    fn set_transfer_mode(&self, _mode: TransferMode) -> Result<()> {
        unimplemented!();
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        Ok(8)
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        match bits_per_word {
            8 => Ok(()),
            _ => Err(SpiError::InvalidWordSize(bits_per_word).into()),
        }
    }

    fn get_max_speed(&self) -> Result<u32> {
        Ok(match self.inner.borrow().spi_clock {
            ClockSpeed::Clk24Mhz => 24_000_000,
            ClockSpeed::Clk12Mhz => 12_000_000,
            ClockSpeed::Clk8Mhz => 8_000_000,
            ClockSpeed::Clk3Mhz => 3_000_000,
            ClockSpeed::Clk2p18Mhz => 2_180_000,
            ClockSpeed::Clk1p5Mhz => 1_500_000,
            ClockSpeed::Clk750Khz => 750_000,
            ClockSpeed::Clk375Khz => 375_000,
        })
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        self.inner.borrow_mut().spi_clock = if frequency >= 24_000_000 {
            ClockSpeed::Clk24Mhz
        } else if frequency >= 12_000_000 {
            ClockSpeed::Clk12Mhz
        } else if frequency >= 8_000_000 {
            ClockSpeed::Clk8Mhz
        } else if frequency >= 3_000_000 {
            ClockSpeed::Clk3Mhz
        } else if frequency >= 2_180_000 {
            ClockSpeed::Clk2p18Mhz
        } else if frequency >= 1_500_000 {
            ClockSpeed::Clk1p5Mhz
        } else if frequency >= 750_000 {
            ClockSpeed::Clk750Khz
        } else {
            ClockSpeed::Clk375Khz
        };
        self.set_spi_clock()
    }

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        Ok(false)
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // Arbitrary value: number of `Transfers` that can be in a single transaction.
        Ok(42)
    }

    /// Maximum `Read` and `Write` data size for `run_transaction()`.
    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: Self::MAX_GENERIC_DATA_LEN,
            write: Self::MAX_GENERIC_DATA_LEN,
        })
    }

    /// Sets the Dediprog voltage to `value` Volts.
    fn set_voltage(&self, voltage: Voltage) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.voltage = if voltage.as_volts() <= 0.3 {
            super::Voltage::V0
        } else if voltage.as_volts() >= 1.6 && voltage.as_volts() <= 2.0 {
            super::Voltage::V1p8
        } else if voltage.as_volts() >= 2.3 && voltage.as_volts() <= 2.7 {
            super::Voltage::V2p5
        } else if voltage.as_volts() >= 3.0 && voltage.as_volts() <= 3.6 {
            super::Voltage::V3p5
        } else {
            bail!(SpiError::InvalidVoltage(voltage))
        };
        inner.set_voltage()
    }

    /// Dediprog has limited support for "plain" SPI transactions.  It can only hold the CS
    /// asserted across a write then optional read, both of at most 16 bytes.
    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        match transaction {
            [] => (),
            [Transfer::Write(wbuf), Transfer::Read(rbuf)] => {
                // Dediprog can do a short SPI write followed by a short SPI read as a single
                // USB request/reply.
                ensure!(
                    wbuf.len() <= Self::MAX_GENERIC_DATA_LEN,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                ensure!(
                    rbuf.len() <= Self::MAX_GENERIC_DATA_LEN,
                    SpiError::InvalidDataLength(rbuf.len())
                );
                self.transmit(wbuf, rbuf.len())?;
                self.receive(rbuf)?;
            }
            [Transfer::Write(wbuf)] => {
                ensure!(
                    wbuf.len() <= Self::MAX_GENERIC_DATA_LEN,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                self.transmit(wbuf, 0)?;
            }
            _ => bail!(SpiError::InvalidTransferMode(
                "Unsupported combination".to_string()
            )),
        }
        Ok(())
    }

    /// Maximum payload size of `Read` and `Write` elements for `run_eeprom_transactions()`.
    fn get_eeprom_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: self.max_chunk_size,
            write: self.max_chunk_size,
        })
    }

    fn run_eeprom_transactions(&self, transactions: &mut [eeprom::Transaction]) -> Result<()> {
        self.do_run_eeprom_transactions(transactions)
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        unimplemented!();
    }
}
