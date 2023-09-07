// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use safe_ftdi as ftdi;
use std::cell::RefCell;
use std::rc::Rc;

use crate::io::spi::{
    AssertChipSelect, ClockPolarity, MaxSizes, SpiError, Target, TargetChipDeassert, Transfer,
    TransferMode,
};
use crate::transport::ultradebug::mpsse;
use crate::transport::ultradebug::Ultradebug;

struct Inner {
    mode: TransferMode,
    cs_asserted_count: u32,
}

/// Represents the Ultradebug SPI device.
pub struct UltradebugSpi {
    pub device: Rc<RefCell<mpsse::Context>>,
    inner: RefCell<Inner>,
}

impl UltradebugSpi {
    pub const PIN_CLOCK: u8 = 0;
    pub const PIN_MOSI: u8 = 1;
    pub const PIN_MISO: u8 = 2;
    pub const PIN_CHIP_SELECT: u8 = 3;
    pub const MASK_CHIP_SELECT: u8 = 1u8 << Self::PIN_CHIP_SELECT;
    pub const PIN_SPI_ZB: u8 = 4;
    pub fn open(ultradebug: &Ultradebug) -> Result<Self> {
        let mpsse = ultradebug.mpsse(ftdi::Interface::B)?;
        // Note: platforms ultradebugs tristate their SPI lines
        // unless SPI_ZB is driven low.  Non-platforms ultradebugs
        // don't use SPI_ZB, so this is safe for both types of devices.
        log::debug!("Setting SPI_ZB");
        mpsse
            .borrow_mut()
            .gpio_set(UltradebugSpi::PIN_SPI_ZB, false)
            .context("FTDI error")?;

        Ok(UltradebugSpi {
            device: mpsse,
            inner: RefCell::new(Inner {
                mode: TransferMode::Mode0,
                cs_asserted_count: 0,
            }),
        })
    }

    fn do_assert_cs(&self, assert: bool) -> Result<()> {
        let device = self.device.borrow();
        // Assert or deassert CS#
        device
            .execute(&mut [mpsse::Command::SetLowGpio(
                device.gpio_direction,
                if assert {
                    device.gpio_value & !Self::MASK_CHIP_SELECT
                } else {
                    device.gpio_value | Self::MASK_CHIP_SELECT
                },
            )])
            .context("FTDI error")?;
        Ok(())
    }
}

impl Target for UltradebugSpi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        Ok(self.inner.borrow().mode)
    }
    fn set_transfer_mode(&self, mode: TransferMode) -> Result<()> {
        self.inner.borrow_mut().mode = mode;
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
        Ok(self.device.borrow().max_clock_frequency)
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        let mut device = self.device.borrow_mut();
        device
            .set_clock_frequency(frequency)
            .context("FTDI error")?;
        Ok(())
    }

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        Ok(true)
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // Arbitrary value: number of `Transfers` that can be in a single transaction.
        Ok(42)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        // Size of the FTDI read buffer.  We can't perform a read larger than this;
        // the FTDI device simply won't read any more.
        Ok(MaxSizes {
            read: 65536,
            write: 65536,
        })
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        let (rdedge, wredge) = match self.inner.borrow().mode.polarity() {
            ClockPolarity::IdleLow => (mpsse::ClockEdge::Rising, mpsse::ClockEdge::Falling),
            ClockPolarity::IdleHigh => (mpsse::ClockEdge::Falling, mpsse::ClockEdge::Rising),
        };

        let mut command = Vec::new();
        let device = self.device.borrow();
        let cs_not_already_asserted = self.inner.borrow().cs_asserted_count == 0;
        if cs_not_already_asserted {
            // Assert CS# (drive low).
            command.push(mpsse::Command::SetLowGpio(
                device.gpio_direction,
                device.gpio_value & !Self::MASK_CHIP_SELECT,
            ));
        }
        // Translate SPI Read/Write Transactions into MPSSE Commands.
        for transfer in transaction.iter_mut() {
            command.push(match transfer {
                Transfer::Read(buf) => mpsse::Command::ReadData(
                    mpsse::DataShiftOptions {
                        read_clock_edge: rdedge,
                        read_data: true,
                        ..Default::default()
                    },
                    buf,
                ),
                Transfer::Write(buf) => mpsse::Command::WriteData(
                    mpsse::DataShiftOptions {
                        write_clock_edge: wredge,
                        write_data: true,
                        ..Default::default()
                    },
                    buf,
                ),
                Transfer::Both(wbuf, rbuf) => mpsse::Command::TransactData(
                    mpsse::DataShiftOptions {
                        write_clock_edge: wredge,
                        write_data: true,
                        ..Default::default()
                    },
                    wbuf,
                    mpsse::DataShiftOptions {
                        read_clock_edge: rdedge,
                        read_data: true,
                        ..Default::default()
                    },
                    rbuf,
                ),
            });
        }
        if cs_not_already_asserted {
            // Release CS# (allow to float high).
            command.push(mpsse::Command::SetLowGpio(
                device.gpio_direction,
                device.gpio_value | Self::MASK_CHIP_SELECT,
            ));
        }
        device.execute(&mut command).context("FTDI error")?;
        Ok(())
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        {
            let mut inner = self.inner.borrow_mut();
            if inner.cs_asserted_count == 0 {
                self.do_assert_cs(true)?;
            }
            inner.cs_asserted_count += 1;
        }
        Ok(AssertChipSelect::new(self))
    }
}

impl TargetChipDeassert for UltradebugSpi {
    fn deassert_cs(&self) {
        let mut inner = self.inner.borrow_mut();
        inner.cs_asserted_count -= 1;
        if inner.cs_asserted_count == 0 {
            // We cannot propagate errors through `Drop::drop()`, so panic on any error.  (Logging
            // would be another option.)
            self.do_assert_cs(false)
                .expect("Error while deasserting CS");
        }
    }
}
