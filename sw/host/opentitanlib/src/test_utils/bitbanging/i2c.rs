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
