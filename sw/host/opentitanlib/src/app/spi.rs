// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::eeprom;
use crate::io::gpio::GpioPin;
use crate::io::spi;
use crate::io::spi::Target;
use crate::transport::Transport;

use anyhow::Result;
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Exactly one `PhysicalSpiWrapper` exists for every underlying tranport `Target` instance that
/// has been accessed through the `TransportWrapper`.  It is used to keep track of which
/// `LogicalSpiWrapper` has already applied its settings to the hardware, in order to avoid
/// repeated invocations of e.g. `set_max_speed()` on the `Target`.
pub struct PhysicalSpiWrapper {
    /// Reference to the `Target` instance of the underlying transport.
    underlying_target: Rc<dyn Target>,
    /// Unique ID of the LogicalSpiWrapper which last used this physical SPI port.
    last_used_by_uid: Cell<Option<usize>>,
}

impl PhysicalSpiWrapper {
    /// Create new instance, should only be called from `TransportWrapper`
    pub fn new(underlying_target: Rc<dyn Target>) -> Self {
        Self {
            underlying_target,
            last_used_by_uid: Cell::new(None),
        }
    }
}

/// Several `LogicalSpiWrapper` objects can exist concurrently, sharing the same underlying
/// transport target, but e.g. having distinct chip select and clock speed settings.  (Terminology
/// is a little muddy here, the underlying object is more properly representing the SPI "bus", and
/// this wrapper a particular target chip on the bus.)
///
/// Calling e.g. `set_max_speed()` on a `LogicalSpiWrapper` will not immediately be propagated to
/// the underlying transport, instead, the accumulated settings are kept in the
/// `LogicalSpiWrapper`, and propagated only whenever an actual SPI transaction is initiated.
pub struct LogicalSpiWrapper {
    /// Reference to the underlying port.
    physical_wrapper: Rc<PhysicalSpiWrapper>,
    /// Unique ID of this `LogicalSpiWrapper`.
    uid: usize,
    // SPI port settings applying to this named logical SPI port.
    mode: Cell<Option<spi::TransferMode>>,
    bits_per_word: Cell<Option<u32>>,
    max_speed: Cell<Option<u32>>,
    chip_select: RefCell<Option<Rc<dyn GpioPin>>>,
}

impl LogicalSpiWrapper {
    /// Create new instance, should only be called from `TransportWrapper`
    pub fn new(
        transport: &dyn Transport,
        conf: &super::SpiConfiguration,
        physical_wrapper: Rc<PhysicalSpiWrapper>,
    ) -> Result<Self> {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Ok(Self {
            physical_wrapper,
            uid: COUNTER.fetch_add(1, Ordering::Relaxed),
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
        if self.physical_wrapper.last_used_by_uid.get() == Some(self.uid) {
            // Physical SPI port last used by this same LogicalSpiWrapper, no need to re-apply our
            // settings.
            return Ok(());
        }
        if let Some(mode) = self.mode.get() {
            self.physical_wrapper
                .underlying_target
                .set_transfer_mode(mode)?;
        }
        if let Some(bits_per_word) = self.bits_per_word.get() {
            self.physical_wrapper
                .underlying_target
                .set_bits_per_word(bits_per_word)?;
        }
        if let Some(max_speed) = self.max_speed.get() {
            self.physical_wrapper
                .underlying_target
                .set_max_speed(max_speed)?;
        }
        if let Some(chip_select) = self.chip_select.borrow().as_ref() {
            self.physical_wrapper
                .underlying_target
                .set_chip_select(chip_select)?;
        }
        Ok(())
    }
}

impl Target for LogicalSpiWrapper {
    fn get_transfer_mode(&self) -> Result<spi::TransferMode> {
        self.physical_wrapper.underlying_target.get_transfer_mode()
    }
    fn set_transfer_mode(&self, mode: spi::TransferMode) -> Result<()> {
        self.mode.set(Some(mode));
        Ok(())
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        self.physical_wrapper.underlying_target.get_bits_per_word()
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        self.bits_per_word.set(Some(bits_per_word));
        Ok(())
    }

    fn get_max_speed(&self) -> Result<u32> {
        self.physical_wrapper.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.max_speed.set(Some(max_speed));
        Ok(())
    }

    fn supports_bidirectional_transfer(&self) -> Result<bool> {
        self.physical_wrapper
            .underlying_target
            .supports_bidirectional_transfer()
    }

    fn set_chip_select(&self, chip_select: &Rc<dyn GpioPin>) -> Result<()> {
        *self.chip_select.borrow_mut() = Some(Rc::clone(chip_select));
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        self.physical_wrapper
            .underlying_target
            .get_max_transfer_count()
    }

    fn get_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.physical_wrapper
            .underlying_target
            .get_max_transfer_sizes()
    }

    fn set_voltage(&self, voltage: crate::util::voltage::Voltage) -> Result<()> {
        self.physical_wrapper.underlying_target.set_voltage(voltage)
    }

    fn run_transaction(&self, transaction: &mut [spi::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.physical_wrapper
            .underlying_target
            .run_transaction(transaction)
    }

    fn get_eeprom_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.physical_wrapper
            .underlying_target
            .get_eeprom_max_transfer_sizes()
    }

    fn run_eeprom_transactions(&self, transactions: &mut [eeprom::Transaction]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.physical_wrapper
            .underlying_target
            .run_eeprom_transactions(transactions)
    }

    fn assert_cs(self: Rc<Self>) -> Result<spi::AssertChipSelect> {
        self.apply_settings_to_underlying()?;
        Rc::clone(&self.physical_wrapper.underlying_target).assert_cs()
    }
}
