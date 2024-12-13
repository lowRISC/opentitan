// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::spi::Transfer;
use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use embedded_hal::spi::SpiBus;

use ftdi_embedded_hal as ftdi_hal;

use crate::io::gpio;
use crate::io::spi::AssertChipSelect;
use crate::io::spi::MaxSizes;
use crate::io::spi::SpiError;
use crate::io::spi::TransferMode;
use crate::transport::Target;
use crate::transport::TransportError;

pub struct Spi<T> {
    spi: Rc<RefCell<ftdi_hal::Spi<ftdi::Device>>>,
    cs: T,
}

impl<T: gpio::GpioPin> Spi<T> {
    pub fn open(
        ftdi_interfaces: &Rc<HashMap<ftdi::Interface, ftdi_hal::FtHal<ftdi::Device>>>,
        cs: T,
    ) -> Result<Self> {
        let hal = ftdi_interfaces
            .get(&ftdi::Interface::B)
            .ok_or_else(|| SpiError::InvalidOption("spi interface".to_owned()))?;
        let spi = hal.spi()?;
        Ok(Spi {
            spi: Rc::new(RefCell::new(spi)),
            cs,
        })
    }

    // Perform a SPI transaction.
    fn spi_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        for transfer in transaction.iter_mut() {
            match transfer {
                Transfer::Read(buf) => self.spi.borrow_mut().read(buf)?,
                Transfer::Write(buf) => self.spi.borrow_mut().write(buf)?,
                Transfer::Both(wbuf, rbuf) => self.spi.borrow_mut().transfer(rbuf, wbuf)?,
                Transfer::TpmPoll => (),
                Transfer::GscReady => (),
            }
        }
        Ok(())
    }
}

impl<T: gpio::GpioPin> Target for Spi<T> {
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
        Ok(6_000_000)
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        log::warn!(
            "set_max_speed to {:?}, but this device doesn't support changing speeds.",
            frequency
        );
        Ok(())
    }

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        Ok(true)
    }

    /// Indicates whether `Transfer::TpmPoll` is supported.
    fn supports_tpm_poll(&self) -> Result<bool> {
        Ok(false)
    }

    fn set_pins(
        &self,
        _serial_clock: Option<&Rc<dyn gpio::GpioPin>>,
        _host_out_device_in: Option<&Rc<dyn gpio::GpioPin>>,
        _host_in_device_out: Option<&Rc<dyn gpio::GpioPin>>,
        _chip_select: Option<&Rc<dyn gpio::GpioPin>>,
        _gsc_ready: Option<&Rc<dyn gpio::GpioPin>>,
    ) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        // Arbitrary value: number of `Transfers` that can be in a single transaction.
        Ok(42)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: 1024,
            write: 1024,
        })
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        // Assert CS# (drive low).
        self.cs.write(false)?;
        // Translate SPI Read/Write Transactions into Chip Whisperer spi operations.
        let result = self.spi_transaction(transaction);
        // Release CS# (allow to float high).
        self.cs.write(true)?;
        result
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
