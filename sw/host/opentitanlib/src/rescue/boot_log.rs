// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use serde::Serialize;
use serde_annotate::Annotate;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;

use crate::rescue::RescueError;
use crate::with_unknown;

with_unknown! {
    pub enum BootSlot: u32 [default = Self::Unknown] {
        Unknown = 0,
        RomExtBootSlotA = 0x5abf68ea,
        RomExtBootSlotB = 0x53ebdf83,
        Bl0BootSlotA = 0xb851f57e,
        Bl0BootSlotB = 0x17cfb6bf,
    }
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct BootLog {
    #[annotate(format=hex)]
    digest: [u32; 8],
    #[annotate(format=hex)]
    identifier: u32,
    #[annotate(format=hex)]
    chip_version: u64,
    rom_ext_slot: BootSlot,
    rom_ext_major: u16,
    rom_ext_minor: u16,
    #[annotate(format=hex)]
    rom_ext_size: u32,
    #[annotate(format=hex)]
    rom_ext_nonce: u64,
    bl0_slot: BootSlot,
    #[annotate(format=hex)]
    reserved: [u32; 15],
}

impl TryFrom<&[u8]> for BootLog {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        if buf.len() < Self::SIZE {
            return Err(RescueError::BadSize(Self::SIZE, buf.len()));
        }
        if !BootLog::valid_digest(buf) {
            return Err(RescueError::InvalidDigest);
        }
        let mut reader = std::io::Cursor::new(buf);
        let mut val = BootLog::default();
        reader.read_u32_into::<LittleEndian>(&mut val.digest)?;
        val.identifier = reader.read_u32::<LittleEndian>()?;
        val.chip_version = reader.read_u64::<LittleEndian>()?;
        val.rom_ext_slot = BootSlot(reader.read_u32::<LittleEndian>()?);
        val.rom_ext_major = reader.read_u16::<LittleEndian>()?;
        val.rom_ext_minor = reader.read_u16::<LittleEndian>()?;
        val.rom_ext_size = reader.read_u32::<LittleEndian>()?;
        val.rom_ext_nonce = reader.read_u64::<LittleEndian>()?;
        val.bl0_slot = BootSlot(reader.read_u32::<LittleEndian>()?);
        reader.read_u32_into::<LittleEndian>(&mut val.reserved)?;
        Ok(val)
    }
}

impl BootLog {
    pub const SIZE: usize = 128;
    const HASH_LEN: usize = 32;

    fn valid_digest(buf: &[u8]) -> bool {
        let mut digest = Sha256::digest(&buf[Self::HASH_LEN..Self::SIZE]);
        digest.reverse();
        digest[..] == buf[..Self::HASH_LEN]
    }
}
