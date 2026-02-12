// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod i2c;
pub mod pwm;
pub mod spi;
pub mod uart;
pub mod uart_rx_sampling;

use serde::{Deserialize, Serialize};

#[repr(u8)]
#[derive(Debug, PartialEq, Clone, Copy, Serialize, Deserialize)]
pub enum Bit {
    Low = 0,
    High = 1,
}

impl From<bool> for Bit {
    fn from(val: bool) -> Self {
        if val { Self::High } else { Self::Low }
    }
}

impl From<u8> for Bit {
    fn from(val: u8) -> Self {
        match val {
            0x00 => Self::Low,
            _ => Self::High,
        }
    }
}
