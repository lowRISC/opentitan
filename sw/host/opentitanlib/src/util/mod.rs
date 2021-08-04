// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::num::ParseIntError;

pub mod bitfield;
pub mod file;

pub fn parse_u16(src: &str) -> Result<u16, ParseIntError> {
    if let Some(val) = src.strip_prefix("0x") {
        u16::from_str_radix(val, 16)
    } else {
        u16::from_str_radix(src, 10)
    }
}
