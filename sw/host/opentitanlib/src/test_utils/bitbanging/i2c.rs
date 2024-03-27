// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Bit {
    Low = 0,
    High = 1,
}

impl std::convert::From<u8> for Bit {
    fn from(val: u8) -> Self {
        match val {
            0x00 => Self::Low,
            0x01 => Self::High,
            _ => panic!("Can't convert"),
        }
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
        Broken(Vec<Bit>),
    }

    impl Transfer<'_> {
        fn bitbaging<const SDA: u8, const SCL: u8>(&self, is_next_stop: bool) -> Vec<u8> {
            match self {
                Transfer::Start => vec![
                    0x01 << SDA | 0x01 << SCL,
                    0x00 << SDA | 0x01 << SCL,
                    0x00 << SDA | 0x00 << SCL,
                ],
                Transfer::Stop => vec![
                    0x00 << SDA | 0x00 << SCL,
                    0x00 << SDA | 0x01 << SCL,
                    0x01 << SDA | 0x01 << SCL,
                ],
                Transfer::Addr { addr, read, nack } => {
                    self.byte::<SDA, SCL>((addr << 1) | *read as u8, *nack)
                }
                Transfer::Write(bytes) => bytes
                    .iter()
                    .flat_map(|byte| self.byte::<SDA, SCL>(*byte, true))
                    .collect(),
                Transfer::Broken(bits) => self.bits::<SDA, SCL>(bits),
                Transfer::Read(len) => (0..*len)
                    .flat_map(|index| {
                        self.byte::<SDA, SCL>(0xff, index >= (len - 1) && !is_next_stop)
                    })
                    .collect(),
            }
        }

        fn byte<const SDA: u8, const SCL: u8>(&self, byte: u8, nack: bool) -> Vec<u8> {
            let mut buffer = (0..8u8)
                .rev()
                .flat_map(|bit| {
                    [
                        (((byte >> bit) & 0x01) << SDA) | 0x01 << SCL,
                        (((byte >> bit) & 0x01) << SDA) | 0x00 << SCL,
                    ]
                })
                .collect::<Vec<u8>>();
            buffer.append(&mut self.nack::<SDA, SCL>(nack));
            buffer
        }

        fn bits<const SDA: u8, const SCL: u8>(&self, bits: &[Bit]) -> Vec<u8> {
            bits.iter()
                .rev()
                .flat_map(|bit| {
                    [
                        ((*bit as u8) << SDA) | 0x01 << SCL,
                        ((*bit as u8) << SDA) | 0x00 << SCL,
                    ]
                })
                .collect::<Vec<u8>>()
        }

        fn nack<const SDA: u8, const SCL: u8>(&self, nack: bool) -> Vec<u8> {
            vec![
                (nack as u8) << SDA | 0x01 << SCL,
                (nack as u8) << SDA | 0x00 << SCL,
            ]
        }
    }
    pub struct Encoder<const SDA: u8, const SCL: u8> {}
    impl<const SDA: u8, const SCL: u8> Encoder<SDA, SCL> {
        pub fn run(&self, transfer: &[Transfer]) -> Vec<u8> {
            let mut result: Vec<u8> = transfer
                .windows(2)
                .flat_map(|window| {
                    window[0].bitbaging::<SDA, SCL>(window.get(1) != Some(&Transfer::Stop))
                })
                .collect();

            //We missed the last element for using the windows function to peek, so we parse the last element here.
            result.append(&mut transfer.iter().last().unwrap().bitbaging::<SDA, SCL>(false));
            result
        }
    }
}
pub mod decoder {
    use super::*;
    use anyhow::{bail, Context, Result};
    use std::iter::Peekable;

    #[derive(Debug, PartialEq)]
    enum Symbol {
        Start,
        Stop,
        Byte { data: u8, nack: bool },
        Broken([Option<Bit>; 8]),
    }

    impl Symbol {
        fn broken(data: u8, bits: usize) -> Result<Self> {
            let mut buffer: [Option<Bit>; 8] = [None; 8];
            if !(1..8).contains(&bits) {
                bail!("Not enough samples");
            }
            for (bit, slot) in buffer.iter_mut().enumerate().take(bits) {
                *slot = Some(Bit::from(data << bit));
            }

            Ok(Self::Broken(buffer))
        }
    }

    #[derive(Debug, PartialEq)]
    pub enum Transfer<'b> {
        Start,
        Stop,
        Addr { addr: u8, read: bool, nack: bool },
        Bytes { data: &'b [u8], nack: bool },
        Broken([Option<Bit>; 8]),
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
        /// Returns a sample when a fall clock edge happen.
        ///         /// The returned sample is taken *before* the falling edge, when SCL is high.
        /// The caller must make sure that the clock was high in the previous sample.
        fn sample_on_fall_edge<I>(samples: &mut Peekable<I>) -> Result<Option<Sample<SDA, SCL>>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            let mut sda = None;
            loop {
                if samples
                    .peek()
                    .context("Ran out of samples and did not find fall edge")?
                    .scl()
                    == Bit::Low
                {
                    return Ok(sda);
                }
                sda = Some(
                    samples
                        .next()
                        .context("Ran out of samples and did not find fall edge")?,
                );
            }
        }

        /// Returns a sample when a raise clock edge happen.
        /// The caller must make sure that the clock was low in the previous sample.
        fn sample_on_raise_edge<I>(samples: &mut Peekable<I>) -> Option<Sample<SDA, SCL>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            samples.by_ref().find(|sample| sample.scl() == Bit::High)
        }

        fn loop_until<I>(samples: &mut Peekable<I>, sda: Bit, scl: Bit) -> Option<Sample<SDA, SCL>>
        where
            I: Iterator<Item = Sample<SDA, SCL>>,
        {
            samples
                .by_ref()
                .find(|sample| sample.sda() == sda && sample.scl() == scl)
        }

        fn find_start<I>(samples: &mut Peekable<I>) -> Result<Sample<SDA, SCL>>
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
            let mut raise_sample: Option<Sample<SDA, SCL>> = None;

            // 8 bits data + 1 bit ack/nack
            for index in 0..9 {
                let Ok(fall_sample) = Self::sample_on_fall_edge(samples) else {
                    return Symbol::broken(byte as u8, index);
                };
                if let (Some(raise), Some(fall)) = (raise_sample, fall_sample) {
                    // if sda transitioned while clock was high, it either mean a stop or start bit.
                    let sda = raise.sda();
                    if fall.sda() != sda {
                        return Ok(match sda {
                            Bit::High => Symbol::Start,
                            Bit::Low => Symbol::Stop,
                        });
                    }
                }

                let Some(sample) = Self::sample_on_raise_edge(samples) else {
                    return Symbol::broken(byte as u8, index);
                };

                byte <<= 1;
                byte |= sample.sda() as u16;
                raise_sample = Some(sample);
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
                            let (filled, empty) = buffer.split_at_mut(head_offset);
                            buffer = empty;
                            head_offset = 0;
                            trans.push(Transfer::Bytes {
                                data: filled,
                                nack: false,
                            });
                            trans.push(symbol.into());
                            DecodingState::Start
                        }
                        _ => panic!("Can't parse {:?}", symbol),
                    },
                }
            }
            Ok(trans)
        }
    }
}
