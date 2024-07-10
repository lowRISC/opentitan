// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod i2c;
pub mod spi;

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
