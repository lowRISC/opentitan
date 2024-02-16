// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use arrayvec::ArrayVec;

#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Bit {
    Low = 0,
    High = 1,
}

impl From<u8> for Bit {
    fn from(val: u8) -> Self {
        match val {
            0x00 => Self::Low,
            _ => Self::High,
        }
    }
}

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
        samples.extend((0..8u8).rev().flat_map(|bit| {
            [
                (((byte >> bit) & 0x01) << SDA) | 0x01 << SCL,
                (((byte >> bit) & 0x01) << SDA) | 0x00 << SCL,
            ]
        }));
        Self::bitbanging_nack::<SDA, SCL>(nack, samples);
    }

    fn bitbanging_bits<const SDA: u8, const SCL: u8>(bits: &[Bit], samples: &mut Vec<u8>) {
        samples.extend(bits.iter().rev().flat_map(|bit| {
            [
                ((*bit as u8) << SDA) | 0x01 << SCL,
                ((*bit as u8) << SDA) | 0x00 << SCL,
            ]
        }));
    }

    fn bitbanging_nack<const SDA: u8, const SCL: u8>(nack: bool, samples: &mut Vec<u8>) {
        samples.extend([
            (nack as u8) << SDA | 0x01 << SCL,
            (nack as u8) << SDA | 0x00 << SCL,
        ]);
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
