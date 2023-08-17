// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use thiserror::Error;

use chrono::{Datelike, Timelike, Utc};
use crc::Crc;

use crate::util::bitfield::BitField;

const SYNC_WORD: [u8; 4] = [0xAA, 0x99, 0x55, 0x66];
const REG_ADDR_USR_ACCESS: u32 = 0x0d;
const REG_ADDR_CRC: u32 = 0x00;
const NOOP: [u8; 4] = [0x20, 0x00, 0x00, 0x00];
const TYPE_FIELD: BitField = BitField {
    offset: 29,
    size: 3,
};
const OP_FIELD: BitField = BitField {
    offset: 27,
    size: 2,
};
const TYPE1_ADDR_FIELD: BitField = BitField {
    offset: 13,
    size: 14,
};
const TYPE1_WORDS_FIELD: BitField = BitField {
    offset: 0,
    size: 11,
};
const TYPE2_WORDS_FIELD: BitField = BitField {
    offset: 0,
    size: 27,
};

#[derive(Error, Debug, Serialize, Deserialize)]
pub enum Error {
    #[error("Command {0:#x?} not found in bitstream")]
    CommandNotFound(u32),
}

#[derive(PartialEq)]
enum BitstreamOp {
    Nop = 0,
    Read = 1,
    Write = 2,
    Reserved,
}

struct BitstreamTypeOnePacketHeader {
    /// The 32-bit word making up the header of the Type 1 packet.
    value: u32,
    /// The byte offset in the bitstream where this word begins.
    offset: usize,
}

impl BitstreamTypeOnePacketHeader {
    fn op(&self) -> BitstreamOp {
        match OP_FIELD.extract(self.value) {
            0 => BitstreamOp::Nop,
            1 => BitstreamOp::Read,
            2 => BitstreamOp::Write,
            _ => BitstreamOp::Reserved,
        }
    }

    fn address(&self) -> u32 {
        TYPE1_ADDR_FIELD.extract(self.value)
    }

    fn data_size(&self) -> usize {
        usize::try_from(4 * TYPE1_WORDS_FIELD.extract(self.value)).unwrap()
    }
}

/// Iterator struct that outputs a sequence of Type 1 packet headers contained in the bitstream.
struct BitstreamTypeOneHeaders<'a> {
    bitstream: &'a [u8],
    offset: usize,
    have_sync: bool,
}

impl<'a> BitstreamTypeOneHeaders<'a> {
    fn from_bitstream(bitstream: &[u8]) -> BitstreamTypeOneHeaders {
        BitstreamTypeOneHeaders {
            bitstream,
            offset: 0,
            have_sync: false,
        }
    }

    /// Finds the index in the `bitstream` slice that represents the beginning of the next sync
    /// word. The search begins from the current offset, and if a sync word is found, returns with
    /// the position of that sync word (indexed from the beginning of the bitstream).
    fn find_next_sync(&self) -> Option<usize> {
        self.bitstream[self.offset..]
            .windows(4)
            .position(|word| *word == SYNC_WORD)
            .map(|offset| self.offset + offset)
    }
}

impl<'a> std::iter::Iterator for BitstreamTypeOneHeaders<'a> {
    type Item = BitstreamTypeOnePacketHeader;

    /// Conditionally returns a BitstreamTypeOnePacketHeader representing the next Type 1 packet
    /// header in the bitstream, starting from the last Type 1 packet header found. Does not wrap
    /// around to the beginning of the bitstream again.
    fn next(&mut self) -> Option<Self::Item> {
        while self.offset + 4 < self.bitstream.len() {
            if !self.have_sync {
                if let Some(sync_offset) = self.find_next_sync() {
                    self.offset = sync_offset + 4;
                    self.have_sync = true;
                } else {
                    self.offset = self.bitstream.len();
                    return None;
                }
            }
            let header = &self.bitstream[self.offset..self.offset + 4];
            let header = u32::from_be_bytes(header.try_into().ok()?);
            let header = match TYPE_FIELD.extract(header) {
                1 => {
                    let x = BitstreamTypeOnePacketHeader {
                        value: header,
                        offset: self.offset,
                    };
                    self.offset += 4 + x.data_size();
                    Some(x)
                }
                2 => {
                    let data_bytes = 4 * TYPE2_WORDS_FIELD.extract(header);
                    self.offset += usize::try_from(4 + data_bytes).unwrap();
                    None
                }
                _ => {
                    log::info!("Bitstream lost sync at {:#x}", self.offset);
                    self.have_sync = false;
                    None
                }
            };
            if header.is_some() {
                return header;
            }
        }
        None
    }
}

/// Assembles a Type 1 header word from the `op` and `address` fields, assuming a single word for
/// the length of the value.
fn cmd_from_parts(op: BitstreamOp, address: u32) -> u32 {
    TYPE_FIELD.emplace(1)
        | OP_FIELD.emplace(op as u32)
        | TYPE1_ADDR_FIELD.emplace(address)
        | TYPE1_WORDS_FIELD.emplace(1)
}

/// Searches for the following pattern in the bitstream
///
/// 0x30000001 (write the following word to the CRC register and check)
/// 0xXXXXXXXX (value to write to the CRC register)
/// 0x20000000 (NOOP)
/// 0x20000000 (NOOP)
///
/// and replaces it with
///
/// 0x20000000 (NOOP)
/// 0x20000000 (NOOP)
/// 0x20000000 (NOOP)
/// 0x20000000 (NOOP)
///
/// to remove the CRC check during FPGA configuration.
fn remove_crc(bitstream: &mut [u8]) {
    let crc_headers: Vec<BitstreamTypeOnePacketHeader> =
        BitstreamTypeOneHeaders::from_bitstream(bitstream)
            .filter(|x| (x.op() == BitstreamOp::Write) && (x.address() == REG_ADDR_CRC))
            .collect();
    for header in crc_headers.iter() {
        log::info!(
            "Replaced WRITE_CRC_REG command at {:#x} with NOOP",
            header.offset
        );
        bitstream[header.offset..header.offset + 4].copy_from_slice(&NOOP);
        bitstream[header.offset + 4..header.offset + 8].copy_from_slice(&NOOP);
    }
}

pub fn usr_access_get(bitstream: &[u8]) -> Result<u32> {
    if let Some(header) = BitstreamTypeOneHeaders::from_bitstream(bitstream)
        .find(|x| (x.op() == BitstreamOp::Write) && (x.address() == REG_ADDR_USR_ACCESS))
    {
        let operand = &bitstream[header.offset + 4..header.offset + 8];
        let usr_access = u32::from_be_bytes(operand.try_into()?);
        log::info!("Bitstream file USR_ACCESS value: {:#x}", usr_access);
        return Ok(usr_access);
    }
    Err(Error::CommandNotFound(cmd_from_parts(BitstreamOp::Write, REG_ADDR_USR_ACCESS)).into())
}

/// Returns a 32-bit timestamp suitable to be used as a USR_ACCESS value:
///
/// |-------+-------+-------+-------------------------+-------+--------+--------|
/// | Bits: | 31:27 | 26:23 | 22:17                   | 16:12 | 11:6   | 5:0    |
/// |-------+-------+-------+-------------------------+-------+--------+--------|
/// | Data: | Day   | Month | Year (since 2000, 0-63) | Hour  | Minute | Second |
/// |-------+-------+-------+-------------------------+-------+--------+--------|
///
/// From
/// <https://www.xilinx.com/content/dam/xilinx/support/documents/application_notes/xapp1232-bitstream-id-with-usr_access.pdf>
pub fn usr_access_timestamp() -> u32 {
    let now = Utc::now();
    now.day() << 27
        | now.month() << 23
        | now.year_ce().1.checked_sub(2000u32).unwrap() << 17
        | now.hour() << 12
        | now.minute() << 6
        | now.second()
}

/// Returns the crc32 hash of the bitstream to be used as a USR_ACCESS value
pub fn usr_access_crc32(bitstream: &mut [u8]) -> Result<u32> {
    usr_access_set(bitstream, 0)?; // Clear usr_access before hashing
    Ok(Crc::<u32>::new(&crc::CRC_32_ISO_HDLC).checksum(bitstream))
}

pub fn usr_access_set(bitstream: &mut [u8], val: u32) -> Result<()> {
    if let Some(header) = BitstreamTypeOneHeaders::from_bitstream(bitstream)
        .find(|x| (x.op() == BitstreamOp::Write) && (x.address() == REG_ADDR_USR_ACCESS))
    {
        let operand = &mut bitstream[header.offset + 4..header.offset + 8];
        let usr_access = u32::from_be_bytes(operand.try_into()?);
        log::info!("Bitstream file old USR_ACCESS value: {:#x}", usr_access);
        operand.copy_from_slice(&val.to_be_bytes());
        log::info!("Bitstream file new USR_ACCESS value: {:#x}", val);
        remove_crc(bitstream);
        return Ok(());
    }
    Err(Error::CommandNotFound(cmd_from_parts(BitstreamOp::Write, REG_ADDR_USR_ACCESS)).into())
}
