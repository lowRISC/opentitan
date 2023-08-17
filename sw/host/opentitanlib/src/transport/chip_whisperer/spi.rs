// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::spi::{AssertChipSelect, MaxSizes, SpiError, Target, Transfer, TransferMode};
use crate::transport::chip_whisperer::usb::Backend;
use crate::transport::chip_whisperer::ChipWhisperer;
use crate::transport::TransportError;

pub struct Spi {
    device: Rc<RefCell<Backend>>,
}

impl Spi {
    pub fn open(device: Rc<RefCell<Backend>>) -> Result<Self> {
        {
            let usb = device.borrow();
            usb.spi1_setpins(
                // For some reason, SDI/SDO are reversed in the python implementation
                // and this seems to be required to make the transport work.
                ChipWhisperer::PIN_SDI,
                ChipWhisperer::PIN_SDO,
                ChipWhisperer::PIN_CLK,
                ChipWhisperer::PIN_CS,
            )?;
            usb.spi1_enable(true)?;

            // Set the JTAG pin to false to use SPI mode.
            usb.pin_set_state(ChipWhisperer::PIN_TAP_STRAP1, false)?;
        }

        Ok(Spi { device })
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

impl Target for Spi {
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
        // FIXME: what is the speed of the SAM3U SPI interface on the Chip Whisperer board?
        Ok(6_000_000)
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        log::warn!(
            "set_max_speed to {:?}, but this device doesn't support changing speeds.",
            frequency
        );
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // Arbitrary value: number of `Transfers` that can be in a single transaction.
        Ok(42)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: 65536,
            write: 65536,
        })
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        // Assert CS# (drive low).
        self.device.borrow().spi1_set_cs_pin(false)?;
        // Translate SPI Read/Write Transactions into Chip Whisperer spi operations.
        let result = self.spi_transaction(transaction);
        // Release CS# (allow to float high).
        self.device.borrow().spi1_set_cs_pin(true)?;
        result
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
