// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::decode;

pub fn hex_string_to_u32_arrayvec<const N: usize>(hex_str: &str) -> Result<ArrayVec<u32, N>> {
    let hex_str_no_sep = hex_str.replace('_', "");
    let hex_str_prefix = "0x";
    let sanitized_hex_str = if hex_str.starts_with(hex_str_prefix) {
        hex_str_no_sep.strip_prefix(hex_str_prefix).unwrap()
    } else {
        hex_str_no_sep.as_str()
    };
    Ok(decode(sanitized_hex_str)?
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<ArrayVec<u32, N>>())
}
