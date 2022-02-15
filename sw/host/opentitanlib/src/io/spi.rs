// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use std::rc::Rc;
use std::str::FromStr;
use structopt::StructOpt;
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::transport::Result;
use crate::util::voltage::Voltage;

#[derive(Debug, StructOpt)]
pub struct SpiParams {
    #[structopt(long, help = "SPI instance", default_value = "0")]
    pub bus: String,

    #[structopt(long, help = "SPI bus speed")]
    pub speed: Option<u32>,

    #[structopt(long, help = "SPI bus voltage", parse(try_from_str = Voltage::from_str))]
    pub voltage: Option<Voltage>,

    #[structopt(long, help = "SPI polarity/phase mode", parse(try_from_str = TransferMode::from_str))]
    pub mode: Option<TransferMode>,
}

impl SpiParams {
    pub fn create(&self, transport: &TransportWrapper) -> Result<Rc<dyn Target>> {
        let spi = transport.spi(&self.bus)?;
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

/// Errors related to the SPI interface and SPI transactions.  These error messages will be
/// printed in the context of a TransportError::SpiError, that is "SPI error: {}".  So including
/// the words "error" or "spi" in texts below will probably be redundant.
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
    #[error("Mismatched data length: {0} != {1}")]
    MismatchedDataLength(usize, usize),
    #[error("Invalid transfer mode: {0}")]
    InvalidTransferMode(String),
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

    fn set_voltage(&self, _voltage: Voltage) -> Result<()> {
        Err(SpiError::InvalidOption("This target does not support set_voltage".to_string()).into())
    }

    /// Runs a SPI transaction composed from the slice of [`Transfer`] objects.
    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()>;
}
