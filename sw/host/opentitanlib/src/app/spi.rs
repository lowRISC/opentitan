// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::eeprom;
use crate::io::gpio::GpioPin;
use crate::io::spi::{self, Target};
use crate::transport::Transport;

use anyhow::Result;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// Several `SpiWrapper` objects can exist concurrently, sharing the same underlying transport
/// target, but e.g. having distinct chip select and clock speed settings.  (Terminology is a
/// little muddy here, the underlying object is more properly representing the SPI "bus", and this
/// wrapper a particular target chip on the bus.)
///
/// Calling e.g. `set_max_speed()` on a `SpiWrapper` will not immediately be propagated to the
/// underlying transport, instead, the accumulated settings are kept in the `SpiWrapper`, and
/// propagated only whenever an actual SPI transaction is initiated.
pub struct SpiWrapper {
    /// Reference to the `Target` instance of the underlying transport.
    underlying_target: Rc<dyn Target>,
    mode: Cell<Option<spi::TransferMode>>,
    bits_per_word: Cell<Option<u32>>,
    max_speed: Cell<Option<u32>>,
    chip_select: RefCell<Option<Rc<dyn GpioPin>>>,
}

impl SpiWrapper {
    pub fn new(transport: &dyn Transport, conf: &super::SpiConfiguration) -> Result<Self> {
        Ok(Self {
            underlying_target: transport.spi(conf.underlying_instance.as_str())?,
            mode: Cell::new(conf.mode),
            bits_per_word: Cell::new(conf.bits_per_word),
            max_speed: Cell::new(conf.bits_per_sec),
            chip_select: RefCell::new(match conf.chip_select {
                Some(ref cs) => Some(transport.gpio_pin(cs.as_str())?),
                None => None,
            }),
        })
    }

    fn apply_settings_to_underlying(&self) -> Result<()> {
        if let Some(mode) = self.mode.get() {
            self.underlying_target.set_transfer_mode(mode)?;
        }
        if let Some(bits_per_word) = self.bits_per_word.get() {
            self.underlying_target.set_bits_per_word(bits_per_word)?;
        }
        if let Some(max_speed) = self.max_speed.get() {
            self.underlying_target.set_max_speed(max_speed)?;
        }
        if let Some(chip_select) = self.chip_select.borrow().as_ref() {
            self.underlying_target.set_chip_select(chip_select)?;
        }
        Ok(())
    }
}

impl Target for SpiWrapper {
    fn get_transfer_mode(&self) -> Result<spi::TransferMode> {
        self.underlying_target.get_transfer_mode()
    }
    fn set_transfer_mode(&self, mode: spi::TransferMode) -> Result<()> {
        self.mode.set(Some(mode));
        Ok(())
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        self.underlying_target.get_bits_per_word()
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        self.bits_per_word.set(Some(bits_per_word));
        Ok(())
    }

    fn get_max_speed(&self) -> Result<u32> {
        self.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.max_speed.set(Some(max_speed));
        Ok(())
    }

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        self.underlying_target.supports_bidirectional_transfer()
    }

    fn set_chip_select(&self, chip_select: &Rc<dyn GpioPin>) -> Result<()> {
        *self.chip_select.borrow_mut() = Some(Rc::clone(chip_select));
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        self.underlying_target.get_max_transfer_count()
    }

    fn get_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.underlying_target.get_max_transfer_sizes()
    }

    fn set_voltage(&self, voltage: crate::util::voltage::Voltage) -> Result<()> {
        self.underlying_target.set_voltage(voltage)
    }

    fn run_transaction(&self, transaction: &mut [spi::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_transaction(transaction)
    }

    fn get_eeprom_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.underlying_target.get_eeprom_max_transfer_sizes()
    }

    fn run_eeprom_transactions(&self, transactions: &mut [eeprom::Transaction]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_eeprom_transactions(transactions)
    }

    fn assert_cs(self: Rc<Self>) -> Result<spi::AssertChipSelect> {
        self.apply_settings_to_underlying()?;
        Rc::clone(&self.underlying_target).assert_cs()
    }
}
