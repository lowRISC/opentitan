// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Args;
use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::str::FromStr;
use thiserror::Error;

use super::eeprom;
use crate::app::TransportWrapper;
use crate::impl_serializable_error;
use crate::util::voltage::Voltage;

#[derive(Clone, Debug, Args, Serialize, Deserialize)]
pub struct SpiParams {
    #[arg(long, help = "SPI instance")]
    pub bus: Option<String>,

    #[arg(long, help = "SPI bus speed")]
    pub speed: Option<u32>,

    #[arg(long, help = "SPI bus voltage")]
    pub voltage: Option<Voltage>,

    #[arg(long, help = "SPI polarity/phase mode")]
    pub mode: Option<TransferMode>,
}

impl SpiParams {
    pub fn create(
        &self,
        transport: &TransportWrapper,
        default_instance: &str,
    ) -> Result<Rc<dyn Target>> {
        let spi = transport.spi(self.bus.as_deref().unwrap_or(default_instance))?;
        if let Some(speed) = self.speed {
            spi.set_max_speed(speed)?;
        }
        if let Some(voltage) = self.voltage {
            spi.set_voltage(voltage)?;
        }
        if let Some(mode) = self.mode {
            spi.set_transfer_mode(mode)?;
        }
        Ok(spi)
    }
}

/// Errors related to the SPI interface and SPI transactions.
#[derive(Error, Debug, Serialize, Deserialize)]
pub enum SpiError {
    #[error("Invalid option: {0}")]
    InvalidOption(String),
    #[error("Invalid word size: {0}")]
    InvalidWordSize(u32),
    #[error("Invalid speed: {0}")]
    InvalidSpeed(u32),
    #[error("Invalid data length: {0}")]
    InvalidDataLength(usize),
    #[error("Invalid data width: {0:?}")]
    InvalidDataWidth(eeprom::DataWidth),
    #[error("Double transfer rate not supported")]
    InvalidDoubleTransferRate(),
    #[error("Invalid number of dummy cycles: {0}")]
    InvalidDummyCycles(u8),
    #[error("Mismatched data length: {0} != {1}")]
    MismatchedDataLength(usize, usize),
    #[error("Invalid transfer mode: {0}")]
    InvalidTransferMode(String),
    #[error("Invalid SPI voltage: {0}")]
    InvalidVoltage(Voltage),
}
impl_serializable_error!(SpiError);

/// Represents the SPI transfer mode.
/// See <https://en.wikipedia.org/wiki/Serial_Peripheral_Interface#Clock_polarity_and_phase>
/// for details about SPI transfer modes.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum TransferMode {
    /// `Mode0` is CPOL=0, CPHA=0.
    Mode0,
    /// `Mode1` is CPOL=0, CPHA=1.
    Mode1,
    /// `Mode2` is CPOL=1, CPHA=0.
    Mode2,
    /// `Mode3` is CPOL=1, CPHA=1.
    Mode3,
}

impl FromStr for TransferMode {
    type Err = SpiError;
    fn from_str(s: &str) -> std::result::Result<TransferMode, Self::Err> {
        match s {
            "Mode0" | "mode0" | "0" => Ok(TransferMode::Mode0),
            "Mode1" | "mode1" | "1" => Ok(TransferMode::Mode1),
            "Mode2" | "mode2" | "2" => Ok(TransferMode::Mode2),
            "Mode3" | "mode3" | "3" => Ok(TransferMode::Mode3),
            _ => Err(SpiError::InvalidTransferMode(s.to_string())),
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ClockPhase {
    SampleLeading,
    SampleTrailing,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ClockPolarity {
    IdleLow,
    IdleHigh,
}

impl TransferMode {
    pub fn phase(&self) -> ClockPhase {
        match self {
            TransferMode::Mode0 | TransferMode::Mode2 => ClockPhase::SampleLeading,
            TransferMode::Mode1 | TransferMode::Mode3 => ClockPhase::SampleTrailing,
        }
    }
    pub fn polarity(&self) -> ClockPolarity {
        match self {
            TransferMode::Mode0 | TransferMode::Mode1 => ClockPolarity::IdleLow,
            TransferMode::Mode2 | TransferMode::Mode3 => ClockPolarity::IdleHigh,
        }
    }
}

/// Represents maximum allowed read or write operation in bytes.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct MaxSizes {
    pub read: usize,
    pub write: usize,
}

/// Represents a SPI transfer.
pub enum Transfer<'rd, 'wr> {
    Read(&'rd mut [u8]),
    Write(&'wr [u8]),
    Both(&'wr [u8], &'rd mut [u8]),
}

/// A trait which represents a SPI Target.
pub trait Target {
    /// Gets the current SPI transfer mode.
    fn get_transfer_mode(&self) -> Result<TransferMode>;
    /// Sets the current SPI transfer mode.
    fn set_transfer_mode(&self, mode: TransferMode) -> Result<()>;

    /// Gets the current number of bits per word.
    fn get_bits_per_word(&self) -> Result<u32>;
    /// Sets the current number of bits per word.
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()>;

    /// Gets the maximum allowed speed of the SPI bus.
    fn get_max_speed(&self) -> Result<u32>;
    /// Sets the maximum allowed speed of the SPI bus.
    fn set_max_speed(&self, max_speed: u32) -> Result<()>;

    /// Returns the maximum number of transfers allowed in a single transaction.
    fn get_max_transfer_count(&self) -> Result<usize>;

    /// Maximum `Read` and `Write` data size for `run_transaction()`.
    fn get_max_transfer_sizes(&self) -> Result<MaxSizes>;

    fn set_voltage(&self, _voltage: Voltage) -> Result<()> {
        Err(SpiError::InvalidOption("This target does not support set_voltage".to_string()).into())
    }

    /// Runs a SPI transaction composed from the slice of [`Transfer`] objects.  Will assert the
    /// CS for the duration of the entire transactions.
    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()>;

    /// Maximum payload size of `Read` and `Write` elements for `run_eeprom_transactions()`.
    fn get_eeprom_max_transfer_sizes(&self) -> Result<MaxSizes> {
        // By default, go by the low-level SPI limits, allowing for 6 bytes of opcode+address+dummy
        let spi_max = self.get_max_transfer_sizes()?;
        Ok(MaxSizes {
            read: spi_max.read,
            write: spi_max.write - 6,
        })
    }

    /// Runs a number of EEPROM/FLASH protocol SPI transactions.  Will assert and deassert CS for
    /// each transaction.
    fn run_eeprom_transactions(&self, transactions: &mut [eeprom::Transaction]) -> Result<()> {
        eeprom::default_run_eeprom_transactions(self, transactions)
    }

    /// Assert the CS signal.  Uses reference counting, will be deasserted when each and every
    /// returned `AssertChipSelect` object have gone out of scope.
    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect>;
}

/// Object that keeps the CS asserted, deasserting when it goes out of scope, (unless another
/// instance keeps CS asserted longer.)
pub struct AssertChipSelect {
    target: Rc<dyn TargetChipDeassert>,
}

impl AssertChipSelect {
    // Needs to be public in order for implementation of `Target` to be able to call it.  Never
    // called by users of `Target`.
    pub fn new(target: Rc<dyn TargetChipDeassert>) -> Self {
        Self { target }
    }
}

impl Drop for AssertChipSelect {
    fn drop(&mut self) {
        self.target.deassert_cs()
    }
}

// Needs to be public in order for implementation of `Target` to be able to implement it.  Never
// called by users of `Target`.
pub trait TargetChipDeassert {
    fn deassert_cs(&self);
}
