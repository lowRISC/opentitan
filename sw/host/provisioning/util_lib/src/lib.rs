// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::decode;
use tiny_keccak::{CShake, Hasher};

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

pub fn hex_string_to_u8_arrayvec<const N: usize>(hex_str: &str) -> Result<ArrayVec<u8, N>> {
    let hex_str_no_sep = hex_str.replace('_', "");
    let hex_str_prefix = "0x";
    let sanitized_hex_str = if hex_str.starts_with(hex_str_prefix) {
        hex_str_no_sep.strip_prefix(hex_str_prefix).unwrap()
    } else {
        hex_str_no_sep.as_str()
    };
    Ok(decode(sanitized_hex_str)?
        .into_iter()
        .collect::<ArrayVec<u8, N>>())
}

// Life cycle tokens are hashed using a keccak hashing algorithm. The result is
// a 16 byte value represented as a vector of two u64s.
pub fn hash_lc_token(input: &[u8]) -> Result<ArrayVec<u64, 2>> {
    let name = b"";
    let customazation = b"LC_CTRL";
    let mut csh = CShake::v128(name, customazation);
    let mut output = [0u8; 16];

    csh.update(input);
    csh.finalize(&mut output);

    Ok(output
        .chunks_exact(8)
        .map(|chunk| {
            let arr: [u8; 8] = chunk.try_into().expect("chunk is the wrong size");
            u64::from_le_bytes(arr)
        })
        .collect::<ArrayVec<u64, 2>>())
}
