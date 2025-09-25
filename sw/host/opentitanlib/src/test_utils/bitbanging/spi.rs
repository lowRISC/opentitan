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
    // TODO: add DDR (Dual Data Rate) support
}

/// Additional delays required to synchronise with a SPI device, all
/// measured in SPI clock cycles (2 bitbanging samples per cycle).
#[derive(Clone, Debug)]
pub struct SpiEncodingDelays {
    pub inter_word_delay: u32,
    pub cs_hold_delay: u32,
    pub cs_release_delay: u32,
}

#[derive(Error, Debug, PartialEq, Serialize, Deserialize)]
pub enum SpiTransferEncodeError {
    #[error("CS must be asserted before bitbanging a SPI transaction.")]
    CsNotAsserted,
}

/// An encoder for SPI transmissions, parameterized over bits in the output
/// bitfields to use for transmission. Does not support encoding as a SPI
/// device (only works as a SPI host).
pub struct SpiBitbangEncoder<
    const D0: u8,
    const D1: u8,
    const D2: u8,
    const D3: u8,
    const CLK: u8,
    const CS: u8,
> {
    pub config: SpiBitbangConfig,
    pub delays: SpiEncodingDelays,
    first_word: bool,
    cs_asserted: bool,
}

// Bits for unused pins should not be used (high-impedance), so default to low.
const UNUSED: Bit = Bit::Low;
const CS_LOW: Bit = Bit::Low;
const CS_HIGH: Bit = Bit::High;

impl<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8>
    SpiBitbangEncoder<D0, D1, D2, D3, CLK, CS>
{
    pub fn new(config: SpiBitbangConfig, delays: SpiEncodingDelays) -> Self {
        Self {
            config,
            delays,
            first_word: true,
            cs_asserted: false,
        }
    }

    // Reset the state of the SPI bitbanging encoder.
    pub fn reset(&mut self) {
        self.first_word = true;
        self.cs_asserted = false;
    }

    // A helper to change the data mode that is used for encoding.
    pub fn set_data_mode(&mut self, mode: SpiDataMode) {
        self.config.data_mode = mode;
    }

    /// Construct a sample bitmap for a set of values on SPI pins
    fn sample(&self, d0: Bit, d1: Bit, d2: Bit, d3: Bit, clk: Bit, cs: Bit) -> u8 {
        ((d0 as u8) << D0)
            | ((d1 as u8) << D1)
            | ((d2 as u8) << D2)
            | ((d3 as u8) << D3)
            | ((clk as u8) << CLK)
            | ((cs as u8) << CS)
    }

    /// Encode up to 4 data bits into 2 bitbanging samples corresponding to 1 SPI clock
    fn encode_data(&self, d0: Bit, d1: Bit, d2: Bit, d3: Bit, samples: &mut Vec<u8>) {
        let clk_idle = Bit::from(self.config.cpol);
        let clk_active = Bit::from(!self.config.cpol);
        samples.extend(if self.config.cpha {
            // CPHA=1, so output bits on (idle->active) edges
            [
                self.sample(d0, d1, d2, d3, clk_active, CS_LOW),
                self.sample(d0, d1, d2, d3, clk_idle, CS_LOW),
            ]
        } else {
            // CPHA=0, so output bits on (active->idle) edges
            [
                self.sample(d0, d1, d2, d3, clk_idle, CS_LOW),
                self.sample(d0, d1, d2, d3, clk_active, CS_LOW),
            ]
        })
    }

    /// Encode 1 SPI word into bitbanging samples. This does not handle
    /// additional logic for wait times and CPHA that must be considered
    /// with the first word.
    fn encode_word(
        &mut self,
        words: &[u8],
        samples: &mut Vec<u8>,
    ) -> Result<(), SpiTransferEncodeError> {
        if !self.cs_asserted {
            return Err(SpiTransferEncodeError::CsNotAsserted);
        }
        if self.first_word {
            self.first_word = false;
        }
        let mut byte = 0x00u8;
        let mut encoded_bits = 0u32; // Count of bits in the current word
        let mut words = words.iter();
        while encoded_bits < self.config.bits_per_word {
            let bits = encoded_bits % 8;
            if bits == 0 {
                if let Some(&next_byte) = words.next() {
                    byte = next_byte;
                } else {
                    break;
                }
            }
            match self.config.data_mode {
                SpiDataMode::Single => {
                    let d0 = Bit::from((byte >> (7 - bits)) & 0x01);
                    self.encode_data(d0, UNUSED, UNUSED, UNUSED, samples);
                    encoded_bits += 1;
                }
                SpiDataMode::Dual => {
                    let d1 = Bit::from((byte >> (7 - bits)) & 0x01);
                    let d0 = Bit::from((byte >> (7 - (bits + 1))) & 0x01);
                    self.encode_data(d0, d1, UNUSED, UNUSED, samples);
                    encoded_bits += 2;
                }
                SpiDataMode::Quad => {
                    let d3 = Bit::from((byte >> (7 - bits)) & 0x01);
                    let d2 = Bit::from((byte >> (7 - (bits + 1))) & 0x01);
                    let d1 = Bit::from((byte >> (7 - (bits + 2))) & 0x01);
                    let d0 = Bit::from((byte >> (7 - (bits + 3))) & 0x01);
                    self.encode_data(d0, d1, d2, d3, samples);
                    encoded_bits += 4;
                }
            }
        }

        // If not enough data is given, pad with 0s until it fits.
        while encoded_bits != 0 && encoded_bits < self.config.bits_per_word {
            match self.config.data_mode {
                SpiDataMode::Single => {
                    self.encode_data(Bit::Low, UNUSED, UNUSED, UNUSED, samples);
                    encoded_bits += 1;
                }
                SpiDataMode::Dual => {
                    self.encode_data(Bit::Low, Bit::Low, UNUSED, UNUSED, samples);
                    encoded_bits += 2;
                }
                SpiDataMode::Quad => {
                    self.encode_data(Bit::Low, Bit::Low, Bit::Low, Bit::Low, samples);
                    encoded_bits += 4;
                }
            }
        }
        Ok(())
    }

    /// Encode a sequence of SPI words into GPIO bitbanging samples.
    fn encode_words(
        &mut self,
        words: &[u8],
        samples: &mut Vec<u8>,
    ) -> Result<(), SpiTransferEncodeError> {
        // Keep encoding words in the data while more exist
        let clk_idle = Bit::from(self.config.cpol);
        let bytes_per_word = self.config.bits_per_word.div_ceil(8) as usize;
        for word in words.chunks(bytes_per_word) {
            if !self.first_word {
                // Optional delays between words
                for _ in 0..(self.delays.inter_word_delay * 2) {
                    samples.push(self.sample(UNUSED, UNUSED, UNUSED, UNUSED, clk_idle, CS_LOW))
                }
            }
            self.encode_word(word, samples)?;
        }
        Ok(())
    }

    /// Output GPIO bitbanging samples for pulling CS low/high (active/inactive).
    pub fn assert_cs(&mut self, assert: bool, samples: &mut Vec<u8>) {
        if (assert && self.cs_asserted) || (!assert && !self.cs_asserted) {
            return;
        }
        self.cs_asserted = assert;
        let clk_idle = Bit::from(self.config.cpol);
        let cs_low = self.sample(UNUSED, UNUSED, UNUSED, UNUSED, clk_idle, CS_LOW);
        if assert {
            // If CPHA=0, we omit the initial CS low sample here as that is
            // combined with the first data write.
            let wait_samples = match self.config.cpha {
                true => self.delays.cs_hold_delay * 2 + 1,
                false => self.delays.cs_hold_delay * 2,
            };
            for _ in 0..wait_samples {
                samples.push(cs_low);
            }
            self.first_word = true;
        } else {
            // If CPHA=0, we must do a final transition of CLK back to idle before
            // we de-assert the CS (not accounting for release delays).
            let wait_samples = match self.config.cpha {
                true => self.delays.cs_release_delay * 2,
                false => self.delays.cs_release_delay * 2 + 1,
            };
            for _ in 0..wait_samples {
                samples.push(cs_low);
            }
            samples.push(self.sample(UNUSED, UNUSED, UNUSED, UNUSED, clk_idle, CS_HIGH));
        }
    }

    /// Encode a read transmission of several SPI words into GPIO bitbanging samples.
    /// CS should already be asserted via `assert_cs` before calling.
    pub fn encode_read(
        &mut self,
        words: usize,
        samples: &mut Vec<u8>,
    ) -> Result<(), SpiTransferEncodeError> {
        self.encode_words(&vec![0; words], samples)
    }

    /// Encode a write transmission of several SPI words into GPIO bitbanging samples.
    /// CS should already be asserted via `assert_cs` before calling.
    pub fn encode_write(
        &mut self,
        data: &[u8],
        samples: &mut Vec<u8>,
    ) -> Result<(), SpiTransferEncodeError> {
        self.encode_words(data, samples)
    }

    /// A helper function to encode a full SPI transmission, including logic for
    /// asserting and later de-asserting the CS.
    pub fn encode_transaction(
        &mut self,
        data: &[u8],
        samples: &mut Vec<u8>,
    ) -> Result<(), SpiTransferEncodeError> {
        self.assert_cs(true, samples);
        self.encode_words(data, samples)?;
        self.assert_cs(false, samples);
        Ok(())
    }
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
            if decoded_bits.is_multiple_of(8) {
                word.push(byte);
                byte = 0x00;
            }
        }
        if !decoded_bits.is_multiple_of(8) {
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

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;
    use std::cmp::Ordering;

    fn spi_encode_decode(
        config: SpiBitbangConfig,
        delays: SpiEncodingDelays,
        data: Option<&[u8]>,
    ) -> Result<()> {
        let bytes_per_word = config.bits_per_word.div_ceil(8) as usize;
        let mut encoder = SpiBitbangEncoder::<0, 1, 2, 3, 4, 5>::new(config.clone(), delays);
        let decoder =
            SpiBitbangDecoder::<0, 1, 2, 3, 4, 5>::new(config.clone(), SpiEndpoint::Device);
        let mut data = Vec::from(data.unwrap_or(b"Hello, this is a simple SPI test message."));
        while data.len() % bytes_per_word != 0 {
            data.push(0);
        }
        let mut samples = Vec::new();
        encoder.encode_transaction(&data, &mut samples)?;
        assert!(!samples.is_empty());
        let decoded = decoder
            .run(samples)
            .expect("Should have decoded the bitbanged message");
        assert_eq!(decoded, data);
        Ok(())
    }

    #[test]
    fn smoke() -> Result<()> {
        // Encode and decode some test strings
        let config = SpiBitbangConfig {
            cpol: false,
            cpha: false,
            data_mode: SpiDataMode::Single,
            bits_per_word: 8,
        };
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 1,
            cs_release_delay: 1,
        };
        spi_encode_decode(config.clone(), delays.clone(), None)?;
        spi_encode_decode(config.clone(), delays.clone(), Some(b"abc def GHI JKL"))?;
        spi_encode_decode(config.clone(), delays.clone(), Some(b"12345678"))?;

        // Check bitbang encoding against a known sample.
        let mut encoder = SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(config, delays);
        let bytes = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        let mut samples = Vec::new();
        encoder.encode_transaction(&bytes, &mut samples)?;
        let expected = [
            0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 0, 1, 0, 1, 0,
            1, 4, 5, 4, 5, 0, 1, 4, 5, 0, 1, 0, 1, 0, 1, 4, 5, 0, 1, 4, 5, 0, 1, 4, 5, 4, 5, 0, 1,
            0, 1, 4, 5, 4, 5, 4, 5, 4, 5, 0, 1, 0, 1, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 4, 5, 0, 1, 4,
            5, 0, 1, 4, 5, 0, 1, 4, 5, 4, 5, 4, 5, 4, 5, 0, 1, 0, 1, 4, 5, 4, 5, 0, 1, 4, 5, 4, 5,
            4, 5, 4, 5, 0, 1, 4, 5, 4, 5, 4, 5, 4, 5, 0, 0, 0, 2,
        ];
        assert_eq!(samples, expected);
        Ok(())
    }

    #[test]
    fn communication_modes() -> Result<()> {
        // Test encoding/decoding all possible modes both with and without
        // additional CS delays on either end, and between words.
        for config_bitmap in 0..32 {
            let config = SpiBitbangConfig {
                cpol: config_bitmap & 0x01 > 0,
                cpha: (config_bitmap >> 1) & 0x01 > 0,
                data_mode: SpiDataMode::Single,
                bits_per_word: 8,
            };
            let delays = SpiEncodingDelays {
                inter_word_delay: (config_bitmap >> 2) & 0x01,
                cs_hold_delay: (config_bitmap >> 3) & 0x01,
                cs_release_delay: (config_bitmap >> 4) & 0x01,
            };
            spi_encode_decode(config.clone(), delays.clone(), None)?;
            spi_encode_decode(config, delays, Some(b"communication mode test message"))?;
        }

        // Use small transfers to test that the output matches what we expect.
        let tests = [
            // CPOL=0,CPHA=0 so bit #1 is output with CS low on idle (low) clock in 1st sample
            ((false, false), vec![4, 5, 0, 1]),
            // CPOL=0,CPHA=1 so bit #1 is output with active (high) clock in 2nd sample
            ((false, true), vec![0, 5, 4, 1]),
            // CPOL=1,CPHA=0 so bit #1 is output with CS low on idle (high) clock in 1st sample
            ((true, false), vec![5, 4, 1, 0]),
            // CPOL=1,CPHA=1 so bit #1 is output with active (low) clock in 2nd sample
            ((true, true), vec![1, 4, 5, 0]),
        ];
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 0,
            cs_release_delay: 0,
        };
        for ((cpol, cpha), expected) in tests {
            let config = SpiBitbangConfig {
                cpol,
                cpha,
                data_mode: SpiDataMode::Single,
                bits_per_word: 8,
            };
            let mut samples = Vec::new();
            SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(config, delays.clone())
                .encode_transaction(&[0xA5], &mut samples)?;
            assert_eq!(samples[..4], expected);
        }
        Ok(())
    }

    #[test]
    fn data_modes() -> Result<()> {
        // Test encoding/decoding for each data channel mode.
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 1,
            cs_release_delay: 1,
        };
        for data_mode in [SpiDataMode::Single, SpiDataMode::Dual, SpiDataMode::Quad] {
            let config = SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode,
                bits_per_word: 8,
            };
            spi_encode_decode(config.clone(), delays.clone(), None)?;
            spi_encode_decode(
                config,
                delays.clone(),
                Some(b"A slightly longer message that can be used to test SPI data modes"),
            )?;
        }

        // Check that the number of transfers is being appropriately decreased.
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 0,
            cs_release_delay: 0,
        };
        let tests = [
            // (64 bits * 2 half clks) + 1 half clk to return to idle + 1 sample for CS high
            (SpiDataMode::Single, 64 * 2 + 2),
            (SpiDataMode::Dual, (64 / 2) * 2 + 2),
            (SpiDataMode::Quad, (64 / 4) * 2 + 2),
        ];
        for (data_mode, expected_half_clocks) in tests {
            let config = SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode,
                bits_per_word: 8,
            };
            let mut samples = Vec::new();
            SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(config, delays.clone()).encode_transaction(
                &[0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF],
                &mut samples,
            )?;
            assert_eq!(samples.len(), expected_half_clocks);
        }
        Ok(())
    }

    #[test]
    fn bits_per_word() -> Result<()> {
        // Test encoding/decoding for a variety of bits per SPI word.
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 1,
            cs_release_delay: 1,
        };
        for bits_per_word in 1..=64 {
            let config = SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode: SpiDataMode::Single,
                bits_per_word,
            };
            // Use a message with [0, 1, 2, ..., 63] bitwise reversed into the MSBs, but for
            // each test we first mask the data so that the unused ending LSBs are zeroed for
            // non-byte-divisible word sizes, to allow comparison of decoded results.
            let mut bytes = (0..64).map(|b: u8| b.reverse_bits()).collect::<Vec<u8>>();
            let mut bits_in_current_word = 0;
            for byte in bytes.iter_mut() {
                let mask_size = bits_per_word - bits_in_current_word;
                match mask_size.cmp(&8) {
                    Ordering::Greater => {
                        bits_in_current_word += 8;
                    }
                    Ordering::Equal => {
                        bits_in_current_word = 0;
                    }
                    Ordering::Less => {
                        let zero_mask = (0x01 << (8 - mask_size)) - 1;
                        *byte &= !zero_mask;
                        bits_in_current_word = 0;
                    }
                }
            }
            spi_encode_decode(config, delays.clone(), Some(&bytes))?;
        }
        Ok(())
    }

    #[test]
    fn encoding_delays() -> Result<()> {
        // Test a variety of SPI encoding delays, with delays after setting CS low,
        // before releasing CS, and between each SPI word transfer.
        let tests = [
            (
                (0, 0, 0),
                vec![4, 5, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 0, 1, 4, 5, 0, 2],
            ),
            (
                (3, 0, 0),
                vec![
                    4, 5, 0, 1, 4, 5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 4, 5, 0, 1, 4, 5, 0, 2,
                ],
            ),
            (
                (0, 3, 0),
                vec![
                    0, 0, 0, 0, 0, 0, 4, 5, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 0, 1, 4, 5, 0, 2,
                ],
            ),
            (
                (0, 0, 3),
                vec![
                    4, 5, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 0, 1, 4, 5, 0, 0, 0, 0, 0, 0, 0, 2,
                ],
            ),
            (
                (1, 2, 3),
                vec![
                    0, 0, 0, 0, 4, 5, 0, 1, 4, 5, 0, 1, 0, 0, 0, 1, 4, 5, 0, 1, 4, 5, 0, 0, 0, 0,
                    0, 0, 0, 2,
                ],
            ),
        ];
        for ((inter_word_delay, cs_hold_delay, cs_release_delay), expected) in tests {
            let delays = SpiEncodingDelays {
                inter_word_delay,
                cs_hold_delay,
                cs_release_delay,
            };
            // Run an encode/decode test with these delays for each CPHA.
            for cpha in [false, true] {
                let config = SpiBitbangConfig {
                    cpol: false,
                    cpha,
                    data_mode: SpiDataMode::Single,
                    bits_per_word: 8,
                };
                spi_encode_decode(config, delays.clone(), None)?;
            }
            let config = SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode: SpiDataMode::Single,
                bits_per_word: 4,
            };
            let mut samples = Vec::new();
            SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(config, delays)
                .encode_transaction(&[0xA << 4, 0x5 << 4], &mut samples)?;
            assert_eq!(samples, expected);
        }
        Ok(())
    }

    #[test]
    fn decoding_endpoints() -> Result<()> {
        // Test decoding as both a SPI Host and Device
        let config = SpiBitbangConfig {
            cpol: false,
            cpha: false,
            data_mode: SpiDataMode::Single,
            bits_per_word: 8,
        };
        let delays = SpiEncodingDelays {
            inter_word_delay: 0,
            cs_hold_delay: 1,
            cs_release_delay: 1,
        };
        let bytes = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        let mut samples = Vec::new();
        // Encode on COPI = D0 = bit 0.
        SpiBitbangEncoder::<0, 1, 2, 3, 4, 5>::new(config.clone(), delays.clone())
            .encode_transaction(&bytes, &mut samples)?;
        // Decode as a SPI Device on COPI = Bit 0
        let decoder =
            SpiBitbangDecoder::<0, 1, 2, 3, 4, 5>::new(config.clone(), SpiEndpoint::Device);
        let mut decoded = decoder
            .run(samples.clone())
            .expect("Should have decoded the bitbanged message");
        assert_eq!(decoded, &bytes);
        // Decode as a SPI Host on CIPO = Bit 0
        let decoder = SpiBitbangDecoder::<1, 0, 2, 3, 4, 5>::new(config.clone(), SpiEndpoint::Host);
        decoded = decoder
            .run(samples)
            .expect("Should have decoded the bitbanged message");
        assert_eq!(decoded, &bytes);
        Ok(())
    }

    #[test]
    fn encode_host_reads() -> Result<()> {
        // Encode a SPI host read
        let mut encoder = SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(
            SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode: SpiDataMode::Single,
                bits_per_word: 8,
            },
            SpiEncodingDelays {
                inter_word_delay: 0,
                cs_hold_delay: 0,
                cs_release_delay: 0,
            },
        );
        let mut samples = Vec::new();
        encoder.assert_cs(true, &mut samples);
        encoder.encode_read(5, &mut samples)?;
        encoder.assert_cs(false, &mut samples);
        // Only expect to see clock changes with CS low, no data.
        let mut expected = vec![0];
        expected.append(&mut [1, 0].repeat(8 * 5)); // clock cycles
        expected.push(2); // CS high (inactive)
        assert_eq!(samples, expected);
        Ok(())
    }

    #[test]
    fn encode_cs_assertions() -> Result<()> {
        // Test errors surrounding CS assertions
        let mut encoder = SpiBitbangEncoder::<2, 3, 4, 5, 0, 1>::new(
            SpiBitbangConfig {
                cpol: false,
                cpha: true,
                data_mode: SpiDataMode::Single,
                bits_per_word: 8,
            },
            SpiEncodingDelays {
                inter_word_delay: 0,
                cs_hold_delay: 0,
                cs_release_delay: 0,
            },
        );
        let mut samples = vec![];
        // No additional samples if already de-asserted
        encoder.assert_cs(false, &mut samples);
        assert_eq!(samples.len(), 0);
        // Do not allow reads/writes if de-asserted
        assert_eq!(
            encoder.encode_write(&[0], &mut samples),
            Err(SpiTransferEncodeError::CsNotAsserted)
        );
        assert_eq!(
            encoder.encode_read(1, &mut samples),
            Err(SpiTransferEncodeError::CsNotAsserted)
        );
        assert_eq!(samples.len(), 0);
        // Samples are encoded on a CS assertion
        encoder.assert_cs(true, &mut samples);
        let mut sample_len = samples.len();
        assert!(sample_len > 0);
        // No additional samples if already asserted
        encoder.assert_cs(true, &mut samples);
        assert_eq!(samples.len(), sample_len);
        // Samples are encoded on a CS de-assertion
        encoder.assert_cs(false, &mut samples);
        assert!(samples.len() > sample_len);
        sample_len = samples.len();
        // No additional samples again if already de-asserted
        encoder.assert_cs(false, &mut samples);
        assert_eq!(samples.len(), sample_len);
        Ok(())
    }

    #[test]
    fn spi_decoding_errors() -> Result<()> {
        // Test clock polarity mismatch errors
        assert_eq!(
            SpiBitbangDecoder::<2, 3, 4, 5, 0, 1>::new(
                SpiBitbangConfig {
                    cpol: false,
                    cpha: false,
                    data_mode: SpiDataMode::Single,
                    bits_per_word: 2,
                },
                SpiEndpoint::Device
            )
            .run(vec![3, 1, 0, 1, 0, 1, 0, 2]),
            Err(SpiTransferDecodeError::ClockPolarityMismatch(
                Bit::High,
                Bit::Low
            ))
        );
        assert_eq!(
            SpiBitbangDecoder::<2, 3, 4, 5, 0, 1>::new(
                SpiBitbangConfig {
                    cpol: true,
                    cpha: false,
                    data_mode: SpiDataMode::Single,
                    bits_per_word: 2,
                },
                SpiEndpoint::Device
            )
            .run(vec![2, 0, 1, 0, 1, 0, 1, 3]),
            Err(SpiTransferDecodeError::ClockPolarityMismatch(
                Bit::Low,
                Bit::High
            ))
        );
        // Test for errors when de-asserting the CS early at any point
        // before a word transfer is finished.
        let valid_samples = vec![4, 5, 0, 1, 4, 5, 0, 1, 0, 1, 4, 5, 0, 1, 4, 5, 0, 2];
        let decoder = SpiBitbangDecoder::<2, 3, 4, 5, 0, 1>::new(
            SpiBitbangConfig {
                cpol: false,
                cpha: false,
                data_mode: SpiDataMode::Single,
                bits_per_word: 8,
            },
            SpiEndpoint::Device,
        );
        assert!(decoder.run(valid_samples.clone()).is_ok());
        for index in 1..(valid_samples.len() - 2) {
            let mut invalid_samples = valid_samples.clone();
            invalid_samples[index] |= 0x01 << 1;
            assert_eq!(
                decoder.run(invalid_samples),
                Err(SpiTransferDecodeError::ChipSelectDeassertedEarly)
            );
        }
        // Test errors with unfinished transactions.
        for index in 2..(valid_samples.len() - 2) {
            let mut invalid_samples = valid_samples.clone();
            invalid_samples.truncate(index);
            assert_eq!(
                decoder.run(invalid_samples),
                Err(SpiTransferDecodeError::UnfinishedTransaction)
            )
        }
        Ok(())
    }
}
