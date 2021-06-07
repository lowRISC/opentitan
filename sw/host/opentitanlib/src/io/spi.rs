// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

/// Represents the SPI transfer mode.
/// See https://en.wikipedia.org/wiki/Serial_Peripheral_Interface#Clock_polarity_and_phase
/// for details about SPI transfer modes.
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

/// Represents a SPI transfer.
pub enum Transfer<'rd, 'wr> {
    Read(&'rd mut [u8]),
    Write(&'wr [u8]),
    Both(&'rd mut [u8], &'wr [u8]),
}

/// A trait which represents a SPI Target.
pub trait Target {
    /// Gets the current SPI transfer mode.
    fn get_transfer_mode(&self) -> Result<TransferMode>;
    /// Sets the current SPI transfer mode.
    fn set_transfer_mode(&mut self, mode: TransferMode) -> Result<()>;

    /// Gets the current number of bits per word.
    fn get_bits_per_word(&self) -> Result<u32>;
    /// Sets the current number of bits per word.
    fn set_bits_per_word(&mut self, bits_per_word: u32) -> Result<()>;

    /// Gets the maximum allowed speed of the SPI bus.
    fn get_max_speed(&self) -> Result<u32>;
    /// Sets the maximum allowed speed of the SPI bus.
    fn set_max_speed(&mut self, max_speed: u32) -> Result<()>;

    /// Returns the maximum number of transfers allowed in a single transaction.
    fn get_max_transfer_count(&self) -> usize;

    /// Runs a SPI transaction composed from the slice of [`Transfer`] objects.
    fn run_transaction(&self, transaction: &[Transfer]) -> Result<()>;
}
