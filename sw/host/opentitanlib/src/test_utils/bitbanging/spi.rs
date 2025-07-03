// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::Bit;
use serde::{Deserialize, Serialize};
use std::iter::Peekable;
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SpiEndpoint {
    Host,   // i.e. "Controller"
    Device, // i.e. "Peripheral"
}

/// The SPI data mode, indicating how many data lines to use for transmission.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum SpiDataMode {
    Single,
    Dual,
    Quad,
}

/// Configuration for SPI bitbanging
#[derive(Clone, Debug)]
pub struct SpiBitbangConfig {
    pub cpol: bool, // Clock polarity
    pub cpha: bool, // Clock Phase
    pub data_mode: SpiDataMode,
    pub bits_per_word: u32,
}

/// A sample of SPI pins at a given instant. The const generics should all be
/// different bit indexes to refer to different pins.
#[derive(Clone, Debug)]
struct Sample<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8> {
    raw: u8,
}

impl<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8>
    Sample<D0, D1, D2, D3, CLK, CS>
{
    fn d0(&self) -> Bit {
        ((self.raw >> D0) & 0x01).into()
    }
    fn d1(&self) -> Bit {
        ((self.raw >> D1) & 0x01).into()
    }
    fn d2(&self) -> Bit {
        ((self.raw >> D2) & 0x01).into()
    }
    fn d3(&self) -> Bit {
        ((self.raw >> D3) & 0x01).into()
    }
    fn clk(&self) -> Bit {
        ((self.raw >> CLK) & 0x01).into()
    }
    fn cs(&self) -> Bit {
        ((self.raw >> CS) & 0x01).into()
    }
}

#[derive(Error, Debug, PartialEq, Serialize, Deserialize)]
pub enum SpiTransferDecodeError {
    #[error("Settings mismatch: Clock level when idle is {0:?}, but cpol expects {1:?}")]
    ClockPolarityMismatch(Bit, Bit),
    #[error("Chip select was de-asserted while a SPI transaction was in progress")]
    ChipSelectDeassertedEarly,
    #[error("Not enough samples were given to complete the SPI transaction")]
    UnfinishedTransaction,
}

/// A decoder for SPI transmissions, parameterized over bits in input sample
/// bitfields of SPI transmissions.
pub struct SpiBitbangDecoder<
    const D0: u8,
    const D1: u8,
    const D2: u8,
    const D3: u8,
    const CLK: u8,
    const CS: u8,
> {
    pub config: SpiBitbangConfig,
    pub endpoint: SpiEndpoint,
}

impl<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8>
    SpiBitbangDecoder<D0, D1, D2, D3, CLK, CS>
{
    pub fn new(config: SpiBitbangConfig, endpoint: SpiEndpoint) -> Self {
        Self { config, endpoint }
    }

    pub fn set_data_mode(&mut self, mode: SpiDataMode) {
        self.config.data_mode = mode;
    }

    /// Iterate through samples until a low (active) CS level is found. Then, check
    /// the clock level based on CPOL config. Returns `true` if a low CS was found.
    fn wait_cs<I>(&self, samples: &mut Peekable<I>) -> Result<bool, SpiTransferDecodeError>
    where
        I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
    {
        let samples = samples.by_ref();
        let clk_idle_level = Bit::from(self.config.cpol);
        while let Some(sample) = samples.peek() {
            if sample.cs() != Bit::Low {
                samples.next();
                continue;
            }
            return if sample.clk() == clk_idle_level {
                Ok(true)
            } else {
                Err(SpiTransferDecodeError::ClockPolarityMismatch(
                    sample.clk(),
                    clk_idle_level,
                ))
            };
        }
        Ok(false)
    }

    /// Get the sample corresponding to the next data bit, directly after an edge
    /// that depends on CPOL/CPHA configuration. Set `first_edge=true` to indicate
    /// that this is the first edge sampled of this SPI word transmission.
    fn sample_on_edge<I>(
        &self,
        samples: &mut I,
        first_edge: bool,
    ) -> Result<Option<Sample<D0, D1, D2, D3, CLK, CS>>, SpiTransferDecodeError>
    where
        I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
    {
        let (wait_level, sample_level) = if self.config.cpol == self.config.cpha {
            (Bit::Low, Bit::High)
        } else {
            (Bit::High, Bit::Low)
        };
        let mut last_sample = None;
        for level in [wait_level, sample_level] {
            let Some(sample) = samples
                .by_ref()
                .find(|sample| sample.clk() == level || sample.cs() == Bit::High)
            else {
                if !first_edge {
                    return Err(SpiTransferDecodeError::UnfinishedTransaction);
                }
                return Ok(None);
            };
            if sample.cs() == Bit::High {
                if !first_edge {
                    return Err(SpiTransferDecodeError::ChipSelectDeassertedEarly);
                }
                return Ok(None);
            }
            last_sample = Some(sample);
        }
        Ok(last_sample)
    }

    /// Decode a SPI word from some input GPIO samples. Returns an error if CS
    /// is deasserted early or the samples are unfinished.
    fn decode_word<I>(&self, samples: &mut I) -> Result<Vec<u8>, SpiTransferDecodeError>
    where
        I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
    {
        let bytes_per_word = self.config.bits_per_word.div_ceil(8) as usize;
        let mut byte: u8 = 0x00;
        let mut decoded_bits = 0u32;
        let mut word: Vec<u8> = Vec::with_capacity(bytes_per_word);
        while decoded_bits < self.config.bits_per_word {
            let Some(sample) = self.sample_on_edge(samples, decoded_bits == 0)? else {
                break;
            };
            match self.config.data_mode {
                SpiDataMode::Single => {
                    byte <<= 1;
                    // In single reads, devices read from COPI whilst hosts read from CIPO.
                    byte |= match self.endpoint {
                        SpiEndpoint::Device => sample.d0() as u8,
                        SpiEndpoint::Host => sample.d1() as u8,
                    };
                    decoded_bits += 1;
                }
                SpiDataMode::Dual => {
                    byte <<= 1;
                    byte |= sample.d1() as u8;
                    byte <<= 1;
                    byte |= sample.d0() as u8;
                    decoded_bits += 2;
                }
                SpiDataMode::Quad => {
                    byte <<= 1;
                    byte |= sample.d3() as u8;
                    byte <<= 1;
                    byte |= sample.d2() as u8;
                    byte <<= 1;
                    byte |= sample.d1() as u8;
                    byte <<= 1;
                    byte |= sample.d0() as u8;
                    decoded_bits += 4;
                }
            }
            if decoded_bits % 8 == 0 {
                word.push(byte);
                byte = 0x00;
            }
        }
        if decoded_bits % 8 != 0 {
            // For < 8 bits per word, we shift partial data back into the MSBs
            byte <<= 8 - (decoded_bits % 8);
            word.push(byte);
        }
        Ok(word)
    }

    /// Decode a full SPI transmission from input GPIO samples, which may contain many
    /// SPI words. Expects CS to be deasserted by the end of all transactions.
    /// Returns the SPI words as a vector of bytes, using the LSBs for partial bytes
    /// (e.g. for 12-bit words, the mask is [0xFF, 0X0F, ...]).
    pub fn run(&self, samples: Vec<u8>) -> Result<Vec<u8>, SpiTransferDecodeError> {
        let mut samples = samples
            .into_iter()
            .map(|raw| Sample::<D0, D1, D2, D3, CLK, CS> { raw })
            .peekable();
        let mut bytes = Vec::new();
        if !self.wait_cs(&mut samples)? {
            return Ok(bytes);
        }
        loop {
            let word = self.decode_word(&mut samples)?;
            if word.is_empty() && !self.wait_cs(&mut samples)? {
                break;
            }
            bytes.extend(word);
        }
        Ok(bytes)
    }
}
