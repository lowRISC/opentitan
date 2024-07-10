// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::Bit;
use anyhow::{bail, Context, Result};

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
    }

    impl<const D0: u8, const D1: u8, const D2: u8, const D3: u8, const CLK: u8, const CS: u8>
        Decoder<D0, D1, D2, D3, CLK, CS>
    {
        /// Returns a sample when a raise or fall clock edge is detected depending on the cpol and cpha configuration.
        fn wait_cs<I>(&self, samples: &mut I) -> Result<()>
        where
            I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
        {
            let clk_idle_level = if self.cpol { Bit::High } else { Bit::Low };

            let sample = samples
                .by_ref()
                .find(|sample| sample.cs() == Bit::Low)
                .expect("Exhausted the samples");
            if sample.clk() == clk_idle_level {
                Ok(())
            } else {
                bail!(
                    "Settings mismatch: Clock level when idle is {:?}, but cpol is {:?}",
                    sample.clk(),
                    self.cpol
                )
            }
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
            samples.by_ref().find(|sample| sample.clk() == wait_level);
            samples.by_ref().find(|sample| sample.clk() == sample_level)
        }

        fn decode_byte<I>(&self, samples: &mut I) -> Result<u8>
        where
            I: Iterator<Item = Sample<D0, D1, D2, D3, CLK, CS>>,
        {
            let mut byte = 0u16;
            let mut bits = 8;
            while bits > 0 {
                let sample = self.sample_on_edge(samples).context("Run out of samples")?;
                match self.data_mode {
                    SpiDataMode::Single => {
                        byte <<= 1;
                        byte |= sample.d0() as u16;
                        bits -= 1;
                    }
                    SpiDataMode::Dual => {
                        byte <<= 1;
                        byte |= sample.d1() as u16;
                        byte <<= 1;
                        byte |= sample.d0() as u16;
                        bits -= 2;
                    }
                    SpiDataMode::Quad => {
                        byte <<= 1;
                        byte |= sample.d3() as u16;
                        byte <<= 1;
                        byte |= sample.d2() as u16;
                        byte <<= 1;
                        byte |= sample.d1() as u16;
                        byte <<= 1;
                        byte |= sample.d0() as u16;
                        bits -= 4;
                    }
                }
            }

            Ok(byte as u8)
        }

        pub fn run(&mut self, samples: Vec<u8>) -> Result<Vec<u8>> {
            let mut samples = samples
                .into_iter()
                .map(|raw| Sample::<D0, D1, D2, D3, CLK, CS> { raw });
            self.wait_cs(&mut samples)?;
            let mut bytes = Vec::new();
            while let Ok(byte) = self.decode_byte(&mut samples) {
                bytes.push(byte);
            }
            Ok(bytes)
        }
    }
}
