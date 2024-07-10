// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use super::Bit;
use anyhow::{bail, Context, Result};
use arrayvec::ArrayVec;

#[derive(Debug, PartialEq)]
enum Symbol {
    Start,
    Stop,
    Byte { data: u8, nack: bool },
    Broken(ArrayVec<Bit, 8>),
}

impl Symbol {
    pub fn broken(data: u8, bits: usize) -> Result<Self> {
        if !(1..8).contains(&bits) {
            bail!("Samples must be between 1 and 7");
        }
        let buffer: ArrayVec<Bit, 8> = (0..bits).map(|bit| Bit::from(data << bit)).collect();

        Ok(Self::Broken(buffer))
    }

    pub fn bitbanging<const SDA: u8, const SCL: u8>(&self, samples: &mut Vec<u8>) {
        match self {
            Symbol::Start => samples.extend([
                0x01 << SDA | 0x01 << SCL,
                0x00 << SDA | 0x01 << SCL,
                0x00 << SDA | 0x00 << SCL,
            ]),
            Symbol::Stop => samples.extend([
                0x00 << SDA | 0x00 << SCL,
                0x00 << SDA | 0x01 << SCL,
                0x01 << SDA | 0x01 << SCL,
            ]),
            Symbol::Byte { data, nack } => Self::bitbanging_byte::<SDA, SCL>(*data, *nack, samples),
            Symbol::Broken(bits) => Self::bitbanging_bits::<SDA, SCL>(bits, samples),
        }
    }

    fn bitbanging_byte<const SDA: u8, const SCL: u8>(byte: u8, nack: bool, samples: &mut Vec<u8>) {
        let data: u16 = (byte as u16) << 1u16 | nack as u16;
        samples.extend((0..9u8).rev().flat_map(|bit| {
            [
                ((((data >> bit) & 0x01) << SDA) | 0x01 << SCL) as u8,
                ((((data >> bit) & 0x01) << SDA) | 0x00 << SCL) as u8,
            ]
        }));
    }

    fn bitbanging_bits<const SDA: u8, const SCL: u8>(bits: &[Bit], samples: &mut Vec<u8>) {
        samples.extend(bits.iter().rev().flat_map(|bit| {
            [
                ((*bit as u8) << SDA) | 0x01 << SCL,
                ((*bit as u8) << SDA) | 0x00 << SCL,
            ]
        }));
    }
}

pub mod encoder {
    use super::*;

    #[derive(Debug, PartialEq)]
    pub enum Transfer<'w> {
        Start,
        Stop,
        Addr { addr: u8, read: bool, nack: bool },
        Write(&'w [u8]),
        Read(usize),
        Broken(ArrayVec<Bit, 8>),
    }

    impl Transfer<'_> {
        fn bitbanging<const SDA: u8, const SCL: u8>(
            &self,
            is_next_stop: bool,
            samples: &mut Vec<u8>,
        ) {
            match self {
                Transfer::Start => Symbol::Start.bitbanging::<SDA, SCL>(samples),
                Transfer::Stop => Symbol::Stop.bitbanging::<SDA, SCL>(samples),
                Transfer::Addr { addr, read, nack } => Symbol::Byte {
                    data: (addr << 1) | *read as u8,
                    nack: *nack,
                }
                .bitbanging::<SDA, SCL>(samples),
                Transfer::Write(bytes) => {
                    for byte in bytes.iter() {
                        Symbol::Byte {
                            data: *byte,
                            nack: true,
                        }
                        .bitbanging::<SDA, SCL>(samples)
                    }
                }
                Transfer::Broken(bits) => {
                    Symbol::Broken(bits.clone()).bitbanging::<SDA, SCL>(samples)
                }
                Transfer::Read(len) => {
                    for index in 0..*len {
                        Symbol::Byte {
                            data: 0xff,
                            nack: index >= (len - 1) && is_next_stop,
                        }
                        .bitbanging::<SDA, SCL>(samples)
                    }
                }
            }
        }
    }

    pub struct Encoder<const SDA: u8, const SCL: u8> {}
    impl<const SDA: u8, const SCL: u8> Encoder<SDA, SCL> {
        pub fn run(&self, transfer: &[Transfer]) -> Vec<u8> {
            let mut samples: Vec<u8> = Vec::new();
            for window in transfer.windows(2) {
                window[0]
                    .bitbanging::<SDA, SCL>(window.get(1) == Some(&Transfer::Stop), &mut samples)
            }

            // We missed the last element for using the windows function to peek, so we parse the last element here.
            transfer
                .iter()
                .last()
                .unwrap()
                .bitbanging::<SDA, SCL>(false, &mut samples);
            samples
        }
    }
}

pub mod decoder {
    use super::*;
    use std::iter::Peekable;

    #[derive(Debug, PartialEq)]
    pub enum Transfer<'b> {
        Start,
        Stop,
        Addr { addr: u8, read: bool, nack: bool },
        Bytes { data: &'b [u8], nack: bool },
        Broken(ArrayVec<Bit, 8>),
    }

    impl<'a> std::convert::From<Symbol> for Transfer<'a> {
        fn from(symbol: Symbol) -> Self {
            match symbol {
                Symbol::Start => Self::Start,
                Symbol::Stop => Self::Stop,
                Symbol::Broken(bits) => Self::Broken(bits),
                _ => panic!("Can't convert {:?} into Transfer", symbol),
            }
        }
    }

    enum DecodingState {
        Start,
        Bytes,
    }

    #[derive(Clone, Debug)]
    struct Sample<const SDA: u8, const SCL: u8> {
        raw: u8,
    }

    impl<const SDA: u8, const SCL: u8> Sample<SDA, SCL> {
        fn sda(&self) -> Bit {
            ((self.raw >> SDA) & 0x01).into()
        }

        fn scl(&self) -> Bit {
            ((self.raw >> SCL) & 0x01).into()
        }
    }
    pub struct Decoder<const SDA: u8, const SCL: u8> {
        pub buffer: [u8; 256],
    }

    impl<const SDA: u8, const SCL: u8> Decoder<SDA, SCL> {
        /// Loops until the clk transitions to low.
        /// Returns a symbol (Start|Stop) in case the sda transitions while the clk is high.
        /// The caller must make sure that the clock was high in the previous sample.
        fn sample_on_fall_edge<I>(samples: &mut I) -> Result<Option<Symbol>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            let mut previous: Option<Sample<SDA, SCL>> = None;
            for sample in samples.by_ref() {
                if sample.scl() == Bit::Low {
                    return Ok(None); // No symbol found.
                }
                // If sda transitioned with the scl high it either means a stop or start symbol.
                if let Some(previous) = previous {
                    if previous.sda() != sample.sda() {
                        return Ok(Some(match sample.sda() {
                            Bit::High => Symbol::Stop,
                            Bit::Low => Symbol::Start,
                        }));
                    }
                }
                previous = Some(sample);
            }
            bail!("Ran out of samples and did not find fall edge")
        }

        /// Returns a sample when a raise clock edge is detected.
        /// This function will not consume the sample where the raise clock is detected.
        /// The caller must make sure that the clock was low in the previous sample.
        fn sample_on_raise_edge<I>(samples: &mut Peekable<I>) -> Option<Sample<SDA, SCL>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            while samples.next_if(|sample| sample.scl() == Bit::Low).is_some() {}
            samples.peek().cloned()
        }

        fn loop_until<I>(samples: &mut I, sda: Bit, scl: Bit) -> Option<Sample<SDA, SCL>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            samples
                .by_ref()
                .find(|sample| sample.sda() == sda && sample.scl() == scl)
        }

        fn find_start<I>(samples: &mut I) -> Result<Sample<SDA, SCL>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            'outer: loop {
                // While clock and sda is not high.
                Self::loop_until(samples, Bit::High, Bit::High)
                    .context("Beginning of start bit not found")?;

                // SDA should transition to low while scl is high, marking the beginning of start condition.
                for sample in samples.by_ref() {
                    if sample.scl() == Bit::Low {
                        continue 'outer;
                    }

                    if sample.sda() == Bit::Low {
                        return Ok(sample);
                    }
                }
                bail!("Start bit condition not found")
            }
        }

        fn decode_symbol<I>(samples: &mut Peekable<I>) -> Result<Symbol>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            let mut byte = 0u16;
            // 8 bits data + 1 bit ack/nack
            for index in 0..9 {
                let Ok(fall_sample) = Self::sample_on_fall_edge(samples) else {
                    return Symbol::broken(byte as u8, index);
                };

                // Return in case a symbol was detected during fall sampling.
                if let Some(symbol) = fall_sample {
                    return Ok(symbol);
                }

                let Some(sample) = Self::sample_on_raise_edge(samples) else {
                    return Symbol::broken(byte as u8, index);
                };
                byte <<= 1;
                byte |= sample.sda() as u16;
            }

            Ok(Symbol::Byte {
                data: (byte >> 1) as u8,
                nack: byte & 0x01 == 1,
            })
        }

        pub fn run(&mut self, samples: Vec<u8>) -> Result<Vec<Transfer<'_>>> {
            let mut samples = samples
                .into_iter()
                .map(|raw| Sample::<SDA, SCL> { raw })
                .peekable();
            Self::find_start(&mut samples)?;
            let mut trans = vec![Transfer::Start];
            let mut state = DecodingState::Start;
            let mut head_offset = 0usize;
            let mut buffer = &mut self.buffer[..];

            while let Ok(symbol) = Self::decode_symbol(&mut samples) {
                state = match state {
                    DecodingState::Start => match symbol {
                        Symbol::Byte { data, nack } => {
                            let read = (data & 1) == 1;
                            trans.push(Transfer::Addr {
                                addr: data >> 1,
                                read,
                                nack,
                            });
                            DecodingState::Bytes
                        }
                        _ => {
                            trans.push(symbol.into());
                            DecodingState::Start
                        }
                    },
                    DecodingState::Bytes => match symbol {
                        Symbol::Byte { data, nack } => {
                            buffer[head_offset] = data;
                            head_offset += 1;
                            assert!(head_offset < buffer.len());
                            if nack {
                                let (filled, empty) = buffer.split_at_mut(head_offset);
                                buffer = empty;
                                head_offset = 0;
                                trans.push(Transfer::Bytes { data: filled, nack });
                                DecodingState::Start
                            } else {
                                DecodingState::Bytes
                            }
                        }
                        Symbol::Start | Symbol::Stop => {
                            if head_offset > 0 {
                                let (filled, empty) = buffer.split_at_mut(head_offset);
                                buffer = empty;
                                head_offset = 0;
                                trans.push(Transfer::Bytes {
                                    data: filled,
                                    nack: false,
                                });
                            }
                            trans.push(symbol.into());
                            DecodingState::Start
                        }
                        Symbol::Broken(_) => {
                            trans.push(symbol.into());
                            DecodingState::Start
                        }
                    },
                }
            }
            Ok(trans)
        }
    }
}
