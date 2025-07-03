// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::Bit;
use anyhow::{bail, Result};
use std::iter::Peekable;

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

pub mod encoder {}

pub mod decoder {
    use super::*;

    #[derive(Clone, Debug)]
    struct Sample<
        const D0: u8,
        const D1: u8,
        const D2: u8,
        const D3: u8,
        const CLK: u8,
        const CS: u8,
    > {
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

    pub struct Decoder<
        const D0: u8,
        const D1: u8,
        const D2: u8,
        const D3: u8,
        const CLK: u8,
        const CS: u8,
    > {
        pub cpol: bool,
        pub cpha: bool,
        pub data_mode: SpiDataMode,
        pub bits_per_word: u32,
        pub endpoint: SpiEndpoint,
    }

    impl<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8>
        Decoder<D0, D1, D2, D3, CLK, CS>
    {
        /// Iterate through samples until a low (active) CS level is found. Then, check
        /// the clock level based on CPOL config. Returns `true` if a low CS was found.
        fn wait_cs<I>(&self, samples: &mut Peekable<I>) -> Result<bool>
        where
            I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
        {
            let clk_idle_level = if self.cpol { Bit::High } else { Bit::Low };
            let samples = samples.by_ref();
            while let Some(sample) = samples.peek() {
                if sample.cs() != Bit::Low {
                    samples.next();
                    continue;
                }
                if sample.clk() == clk_idle_level {
                    return Ok(true);
                } else {
                    bail!(
                        "Settings mismatch: Clock level when idle is {:?}, but cpol is {:?}",
                        sample.clk(),
                        self.cpol
                    )
                }
            }
            Ok(false)
        }
        /// Returns a sample when a raise or fall clock edge is detected depending on the cpol and cpha configuration.
        fn sample_on_edge<I>(&self, samples: &mut I) -> Option<Sample<D0, D1, D2, D3, CLK, CS>>
        where
            I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
        {
            let (sample_level, wait_level) = if self.cpol == self.cpha {
                (Bit::High, Bit::Low)
            } else {
                (Bit::Low, Bit::High)
            };
            samples
                .by_ref()
                .find(|sample| sample.clk() == wait_level || sample.cs() == Bit::High)?;
            samples
                .by_ref()
                .find(|sample| sample.clk() == sample_level || sample.cs() == Bit::High)
        }

        fn decode_word<I>(&self, samples: &mut I) -> Vec<u8>
        where
            I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
        {
            let bytes_per_word = self.bits_per_word.div_ceil(8) as usize;
            let mut byte = 0u8;
            let mut decoded_bits = 0u32;
            let mut word: Vec<u8> = Vec::with_capacity(bytes_per_word);
            while decoded_bits < self.bits_per_word {
                let Some(sample) = self.sample_on_edge(samples) else {
                    break;
                };
                if sample.cs() == Bit::High {
                    break;
                }
                match self.data_mode {
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
            word
        }

        pub fn run(&mut self, samples: Vec<u8>) -> Result<Vec<u8>> {
            let mut samples = samples
                .into_iter()
                .map(|raw| Sample::<D0, D1, D2, D3, CLK, CS> { raw })
                .peekable();
            let mut bytes = Vec::new();
            if !self.wait_cs(&mut samples)? {
                return Ok(bytes);
            }
            loop {
                let word = self.decode_word(&mut samples);
                if word.is_empty() && !self.wait_cs(&mut samples)? {
                    break;
                }
                bytes.extend(word);
            }
            Ok(bytes)
        }
    }
}
