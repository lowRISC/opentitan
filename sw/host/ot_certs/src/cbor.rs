// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};

// For CBOR specification, it's defined in Concise Binary Object Representation (CBOR)
// (https://datatracker.ietf.org/doc/html/rfc8949).

// Section 3.1 Major Types
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[repr(u8)]
enum MajorType {
    Uint = 0,
    Sint = 1,
    Bstr = 2,
    Tstr = 3,
    Array = 4,
    Map = 5,
}

// Section 3 Specification of the CBOR Encoding
// The value of additionial information, describing the type of the argument.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[repr(u8)]
enum ArgType {
    U8 = 24,
    U16 = 25,
    U32 = 26,
    U64 = 27,
}

/// Given a CBOR argument, it returns:
///   1. how many additional bytes to encode them
///   2. the value to be filled in the header's additional information
pub fn arg_size(arg: u64) -> (u64, u8) {
    if arg <= ArgType::U8 as u64 {
        (0, arg as u8)
    } else if arg <= u8::MAX.into() {
        (1, ArgType::U8 as u8)
    } else if arg <= u16::MAX.into() {
        (2, ArgType::U16 as u8)
    } else if arg <= u32::MAX.into() {
        (4, ArgType::U32 as u8)
    } else {
        (8, ArgType::U64 as u8)
    }
}

// The first few bytes of each data item,
// consisting of major type, additional information and argument.
fn header(kind: MajorType, arg: u64) -> Vec<u8> {
    let (size, info) = arg_size(arg);
    // big-endian
    let bytes = (0..size).map(|i| ((arg >> (i * 8)) & 0xff) as u8).rev();
    let mut res = vec![((kind as u8) << 5) | info];
    res.extend(bytes);
    res
}

pub fn int(value: i64) -> Vec<u8> {
    if value >= 0 {
        header(MajorType::Uint, value as u64)
    } else {
        header(MajorType::Sint, -(value + 1) as u64)
    }
}

pub fn byte_array_header(len: u64) -> Vec<u8> {
    header(MajorType::Bstr, len)
}

pub fn string_header(len: u64) -> Vec<u8> {
    header(MajorType::Tstr, len)
}

pub fn array_header(len: u64) -> Vec<u8> {
    header(MajorType::Array, len)
}

pub fn map_header(len: u64) -> Vec<u8> {
    header(MajorType::Map, len)
}
