// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use thiserror::Error;

use chrono::{Datelike, Timelike, Utc};
use crc::Crc;

const SYNC_WORD: [u8; 4] = [0xAA, 0x99, 0x55, 0x66];
const WRITE_USR_ACCESS: [u8; 4] = [0x30, 0x01, 0xa0, 0x01];
const WRITE_CRC_REG: [u8; 4] = [0x30, 0x00, 0x00, 0x01];
const NOOP: [u8; 4] = [0x20, 0x00, 0x00, 0x00];

#[derive(Error, Debug, Serialize, Deserialize)]
pub enum Error {
    #[error("Command {0:#x?} not found in bitstream")]
    CommandNotFound(u32),
}

fn find_cmd(bitstream: &[u8], cmd: &[u8; 4]) -> Result<usize> {
    let sync_offset = bitstream
        .windows(4)
        .enumerate()
        .find(|(_, word)| *word == SYNC_WORD)
        .ok_or_else(|| Error::CommandNotFound(u32::from_be_bytes(SYNC_WORD)))?
        .0;
    let bitstream_no_header = &bitstream[sync_offset..];
    Ok(bitstream_no_header
        .chunks(4)
        .enumerate()
        .find(|(_, op)| *op == cmd)
        .ok_or_else(|| Error::CommandNotFound(u32::from_be_bytes(*cmd)))?
        .0
        * 4
        + sync_offset)
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
    let mut start = 0;
    while start < bitstream.len() {
        match find_cmd(&bitstream[start..], &WRITE_CRC_REG) {
            Ok(mut i) => {
                i += start;
                if (i + 16) <= bitstream.len()
                    && bitstream[i + 8..i + 12] == NOOP
                    && bitstream[i + 12..i + 16] == NOOP
                {
                    log::info!("Replaced WRITE_CRC_REG command at {:#x} with NOOP", i);
                    bitstream[i..i + 4].copy_from_slice(&NOOP);
                    bitstream[i + 4..i + 8].copy_from_slice(&NOOP);
                }
                start = i + 16;
            }
            _ => return,
        }
    }
}

pub fn usr_access_get(bitstream: &[u8]) -> Result<u32> {
    let i = find_cmd(bitstream, &WRITE_USR_ACCESS)?;
    if (i + 8) > bitstream.len() {
        return Err(Error::CommandNotFound(u32::from_be_bytes(WRITE_USR_ACCESS)).into());
    }
    let operand = &bitstream[i + 4..i + 8];
    let usr_access = u32::from_be_bytes(operand.try_into()?);
    log::info!("Bitstream file USR_ACCESS value: {:#x}", usr_access);
    Ok(usr_access)
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
    let i = find_cmd(bitstream, &WRITE_USR_ACCESS)?;
    log::info!(
        "Bitstream file old USR_ACCESS value: {:#x}",
        u32::from_be_bytes(bitstream[i + 4..i + 8].try_into()?)
    );
    bitstream[i + 4..i + 8].copy_from_slice(&val.to_be_bytes());
    log::info!("Bitstream file new USR_ACCESS value: {:#x}", val);
    remove_crc(bitstream);
    Ok(())
}
