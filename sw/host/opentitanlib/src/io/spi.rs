// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use thiserror::Error;

/// Errors related to the SPI interface and SPI transactions.
#[derive(Error, Debug)]
pub enum SpiError {
    #[error("Invalid word size: {0}")]
    InvalidWordSize(u32),
    #[error("Invalid speed: {0}")]
    InvalidSpeed(u32),
}

/// Represents the SPI transfer mode.
/// See https://en.wikipedia.org/wiki/Serial_Peripheral_Interface#Clock_polarity_and_phase
/// for details about SPI transfer modes.
#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Clone, Copy)]
pub enum ClockPhase {
    SampleLeading,
    SampleTrailing,
}

#[derive(Debug, Clone, Copy)]
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
    fn get_max_transfer_count(&self) -> usize;

    /// Maximum chunksize handled by this SPI device.
    fn max_chunk_size(&self) -> usize;

    /// Runs a SPI transaction composed from the slice of [`Transfer`] objects.
    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()>;
}
