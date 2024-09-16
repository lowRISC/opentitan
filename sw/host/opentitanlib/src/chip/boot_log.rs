// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt};
use serde::Serialize;
use serde_annotate::Annotate;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;

use super::boot_svc::BootSlot;
use super::ChipDataError;
use crate::with_unknown;

with_unknown! {
    pub enum OwnershipState: u32 [default = Self::Recovery] {
        Recovery = 0,
        LockedOwner = 0x444e574f,
        UnlockedSelf = 0x464c5355,
        UnlockedAny = 0x594e4155,
        UnlockedEndorsed = 0x444e4555,
    }

}

/// The BootLog provides information about how the ROM and ROM_EXT
/// booted the chip.
#[derive(Debug, Default, Serialize, Annotate)]
pub struct BootLog {
    /// A SHA256 digest over all other fields in this struct.
    #[annotate(format=hex)]
    pub digest: [u32; 8],
    /// A tag that identifies this struct as the boot log ('BLOG').
    #[annotate(format=hex)]
    pub identifier: u32,
    /// The chip version (a git hash prefix from the ROM).
    #[annotate(format=hex)]
    pub chip_version: u64,
    /// The boot slot the ROM chose to boot the ROM_EXT.
    pub rom_ext_slot: BootSlot,
    /// The ROM_EXT major version number.
    pub rom_ext_major: u32,
    /// The ROM_EXT minor version number.
    pub rom_ext_minor: u32,
    /// The ROM_EXT size in bytes.
    #[annotate(format=hex)]
    pub rom_ext_size: u32,
    /// The ROM_EXT nonce (a value used to prevent replay of signed commands).
    #[annotate(format=hex)]
    pub rom_ext_nonce: u64,
    /// The boot slot the ROM_EXT chose to boot the owner firmware.
    pub bl0_slot: BootSlot,
    /// The chip's ownership state.
    pub ownership_state: OwnershipState,
    /// Reserved for future use.
    #[annotate(format=hex)]
    pub reserved: [u32; 13],
}

impl TryFrom<&[u8]> for BootLog {
    type Error = ChipDataError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        if buf.len() < Self::SIZE {
            return Err(ChipDataError::BadSize(Self::SIZE, buf.len()));
        }
        if !BootLog::valid_digest(buf) {
            return Err(ChipDataError::InvalidDigest);
        }
        let mut reader = std::io::Cursor::new(buf);
        let mut val = BootLog::default();
        reader.read_u32_into::<LittleEndian>(&mut val.digest)?;
        val.identifier = reader.read_u32::<LittleEndian>()?;
        val.chip_version = reader.read_u64::<LittleEndian>()?;
        val.rom_ext_slot = BootSlot(reader.read_u32::<LittleEndian>()?);
        val.rom_ext_major = reader.read_u32::<LittleEndian>()?;
        val.rom_ext_minor = reader.read_u32::<LittleEndian>()?;
        val.rom_ext_size = reader.read_u32::<LittleEndian>()?;
        val.rom_ext_nonce = reader.read_u64::<LittleEndian>()?;
        val.bl0_slot = BootSlot(reader.read_u32::<LittleEndian>()?);
        val.ownership_state = OwnershipState(reader.read_u32::<LittleEndian>()?);
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
