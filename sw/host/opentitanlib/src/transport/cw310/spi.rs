// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use log;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::spi::{SpiError, Target, Transfer, TransferMode};
use crate::transport::cw310::usb::Backend;
use crate::transport::cw310::CW310;
use crate::transport::Result;

pub struct CW310Spi {
    device: Rc<RefCell<Backend>>,
}

impl CW310Spi {
    pub fn open(device: Rc<RefCell<Backend>>) -> Result<Self> {
        {
            let usb = device.borrow();
            usb.spi1_setpins(
                // For some reason, SDI/SDO are reversed in the python implementation
                // and this seems to be required to make the transport work.
                CW310::PIN_SDI,
                CW310::PIN_SDO,
                CW310::PIN_CLK,
                CW310::PIN_CS,
            )?;
            usb.spi1_enable(true)?;

            // Set the JTAG pin to false to use SPI mode.
            usb.pin_set_state(CW310::PIN_JTAG, false)?;
        }

        Ok(CW310Spi { device })
    }

    // Perform a SPI transaction.
    fn spi_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        let usb = self.device.borrow();
        for transfer in transaction.iter_mut() {
            match transfer {
                Transfer::Read(buf) => usb.spi1_read(buf)?,
                Transfer::Write(buf) => usb.spi1_write(buf)?,
                Transfer::Both(wbuf, rbuf) => usb.spi1_both(wbuf, rbuf)?,
            }
        }
        Ok(())
    }
}

impl Target for CW310Spi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        Ok(TransferMode::Mode0)
    }
    fn set_transfer_mode(&self, mode: TransferMode) -> Result<()> {
        log::warn!(
            "set_transfer_mode to {:?}, but only Mode0 is supported on this device",
            mode
        );
        Ok(())
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
        // FIXME: what is the speed of the SAM3U SPI interface on the CW310 board?
        Ok(6_000_000)
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        log::warn!(
            "set_max_speed to {:?}, but this device doesn't support changing speeds.",
            frequency
        );
        Ok(())
    }

    fn get_max_transfer_count(&self) -> usize {
        // Arbitrary value: number of `Transfers` that can be in a single transaction.
        42
    }

    fn max_chunk_size(&self) -> usize {
        65536
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        // Assert CS# (drive low).
        self.device.borrow().spi1_set_cs_pin(false)?;
        // Translate SPI Read/Write Transactions into CW310 spi operations.
        let result = self.spi_transaction(transaction);
        // Release CS# (allow to float high).
        self.device.borrow().spi1_set_cs_pin(true)?;
        result
    }
}
