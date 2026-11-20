// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use std::cell::RefCell;
use std::io::{self, Error, ErrorKind, Read, Write};
use std::rc::Rc;
use std::time::{Duration, Instant};

use opentitanlib::io::eeprom;
use opentitanlib::io::eeprom::Transaction::{Read as SpiRead, WaitForBusyClear, Write as SpiWrite};
use opentitanlib::io::spi::{AssertChipSelect, MaxSizes, SpiError, Target, Transfer, TransferMode};
use opentitanlib::spiflash::flash::SpiFlash;
use opentitanlib::util::voltage::Voltage;
use crate::Inner;

pub struct QEMUSpi {
    inner: Rc<RefCell<Inner>>,
    buffer: Rc<RefCell<Vec<u8>>>,
    max_chunk_size: usize,
    spi_mode: u8,
    addr4b_enable: bool,
}

impl QEMUSpi {
    const MAX_FLASH_DATA_LEN: usize = 65536;
    const COMM_TIMEOUT: Duration = Duration::from_millis(2000);

    pub fn open(inner: Rc<RefCell<Inner>>) -> Result<Self> {
        let this = Self {
            inner,
            buffer: Rc::new(RefCell::new(Vec::new())),
            max_chunk_size: 65535 * 256,
            spi_mode: 0,
            addr4b_enable: false,
        };
        Ok(this)
    }

    fn eeprom_read_transaction(&self, cmd: &eeprom::Cmd, rbuf: &mut [u8]) -> Result<()> {
        let cmdbuf = cmd.to_bytes()?;
        self.transmit(cmdbuf, rbuf, true)
    }

    fn eeprom_write_transaction(&self, cmd: &eeprom::Cmd, wbuf: &[u8],
                                _wait_for_busy_clear: bool) -> Result<()> {
        let cmdbuf = cmd.to_bytes()?;
        let mut rbuf = [0u8; 0];
        self.transmit(cmdbuf, &mut rbuf, false)?;
        self.transmit(wbuf, &mut rbuf, true)
    }

    fn do_run_eeprom_transactions(
        &self,
        mut transactions: &mut [eeprom::Transaction],
    ) -> Result<()> {
        loop {
            match transactions {
                [eeprom::Transaction::Command(pre_cmd), SpiWrite(cmd, wbuf), WaitForBusyClear, rest @ ..] =>
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
                &mut [SpiRead(ref mut cmd, ref mut rbuf), ref mut rest @ ..] => {
                    transactions = rest;
                    self.eeprom_read_transaction(cmd, rbuf)?;
                }
                [SpiWrite(cmd, wbuf), WaitForBusyClear, rest @ ..] => {
                    transactions = rest;
                    self.eeprom_write_transaction(cmd, wbuf, true)?;
                }
                [SpiWrite(cmd, wbuf), rest @ ..] => {
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
        Ok(())
    }

    fn build_cs_header(&self, size: usize, release: bool) -> [u8; 8] {
        let mut mode = self.spi_mode & 0xf;
        if !release {
            mode |= 0x80;
        }
        let mut header = [0u8; 8];
        header[0..3].clone_from_slice(b"/CS");
        header[3] = 0; // version
        header[4] = mode;
        header[6..8].clone_from_slice(&(size as u16).to_le_bytes());
        header
    }

    fn send(&self, txbuf: &[u8], release: bool) -> Result<()> {
        let size = txbuf.len();
        let header = self.build_cs_header(size, release);
        {
            let stream = &mut self.inner.borrow_mut().stream;
            stream.write_all(&header[..])
                .with_context(|| "Cannot send SPI CS header")?;
            stream.write_all(txbuf)
                .with_context(|| "Cannot send SPI TX data")
        }
    }

    fn receive(&self, rxbuf: &mut [u8]) -> Result<()> {
        let length = rxbuf.len();
        let mut rx_len = 0usize;
        let timeout = Instant::now() + QEMUSpi::COMM_TIMEOUT;
        while rx_len < length {
            match self.inner.borrow_mut().stream.read(&mut rxbuf[rx_len..length]) {
                Ok(0) => (),
                Ok(n) => { rx_len += n; continue; },
                Err(err) => match err.kind() {
                    ErrorKind::TimedOut | ErrorKind::WouldBlock => (),
                    _ => {
                        return Err(err).with_context(|| "Cannot receive SPI RX data");
                    }
                }
            }
            if Instant::now() > timeout {
                return Err(Error::new(ErrorKind::TimedOut, ""))
                    .with_context(|| "Timeout on SPI RX data");
            }
        }
        Ok(())
    }

    fn transmit(&self, txbuf: &[u8], rxbuf: &mut [u8], release: bool) -> Result<()> {
        let txlen = txbuf.len();
        let rxlen = rxbuf.len();
        let length = txlen+rxlen;
        let mut buffer = self.buffer.borrow_mut();
        buffer.resize(length, 0xffu8);
        buffer[..txlen].clone_from_slice(txbuf);
        log::debug!("TX: {:x?}", buffer);
        self.send(&buffer, release)?;
        buffer.resize(length, 0xffu8);
        self.receive(&mut buffer)?;
        log::debug!("RX: {:x?}", buffer);
        rxbuf.clone_from_slice(&buffer[txlen..]);
        if rxlen != rxbuf.len() {
            return Err(Error::new(ErrorKind::TimedOut, ""))
                .with_context(|| format!("Response truncated {}/{}", rxlen, txlen))
        }
        Ok(())
    }
}

impl Target for QEMUSpi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        unimplemented!();
    }

    fn set_transfer_mode(&self, _mode: TransferMode) -> Result<()> {
        unimplemented!();
    }

    fn supports_tpm_poll(&self) -> Result<bool> {
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
        Ok(10_000_000)
    }

    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // Arbitrary value
        Ok(42)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: Self::MAX_FLASH_DATA_LEN,
            write: Self::MAX_FLASH_DATA_LEN,
        })
    }

    fn set_voltage(&self, voltage: Voltage) -> Result<()> {
        Ok(())
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        match transaction {
            [] => (),
            [Transfer::Write(wbuf), Transfer::Read(rbuf)] => {
                ensure!(
                    wbuf.len() <= Self::MAX_FLASH_DATA_LEN,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                ensure!(
                    rbuf.len() <= Self::MAX_FLASH_DATA_LEN,
                    SpiError::InvalidDataLength(rbuf.len())
                );
                self.transmit(wbuf, rbuf, true)?;
            }
            [Transfer::Write(wbuf)] => {
                ensure!(
                    wbuf.len() <= Self::MAX_FLASH_DATA_LEN,
                    SpiError::InvalidDataLength(wbuf.len())
                );
                let mut rbuf = [0u8; 0];
                self.transmit(wbuf, &mut rbuf, true)?;
            }
            _ => bail!(SpiError::InvalidTransferMode(
                "Unsupported combination".to_string()
            )),
        }
        Ok(())
    }

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

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        Ok(true)
    }
}
