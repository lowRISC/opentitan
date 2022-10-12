// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use byteorder::{LittleEndian, ReadBytesExt};
use num_enum::FromPrimitive;
use serde::Serialize;
use std::convert::TryFrom;
use thiserror::Error;

use crate::util::bitfield::BitField;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    TryFromIntError(#[from] std::num::TryFromIntError),
    #[error("the range {0}..{1} is out of bounds")]
    SliceRange(usize, usize),
    #[error("SFDP header contains incorrect signature: {0:#010x}")]
    WrongHeaderSignature(u32),

    // This is only needed to meet the error conversion requirements for the most
    // general case in the field! macro below.
    #[error(transparent)]
    Infallible(#[from] std::convert::Infallible),
}

/// The SFDP header identifies a valid SFDP, its version and the number of parameter headers.
#[derive(Debug, Serialize)]
pub struct SfdpHeader {
    pub signature: u32,
    pub minor: u8,
    pub major: u8,
    pub nph: u8,
    pub reserved: u8,
}

impl TryFrom<&[u8]> for SfdpHeader {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        const SFDP_HEADER_SIGNATURE: u32 = 0x50444653;

        let mut reader = std::io::Cursor::new(buf);
        let header = SfdpHeader {
            signature: reader.read_u32::<LittleEndian>()?,
            minor: reader.read_u8()?,
            major: reader.read_u8()?,
            nph: reader.read_u8()?,
            reserved: reader.read_u8()?,
        };
        match header.signature {
            SFDP_HEADER_SIGNATURE => Ok(header),
            v => Err(Error::WrongHeaderSignature(v)),
        }
    }
}

/// The SFDP parameter header identifies additional parameter tables within the SFDP.
/// All devices are required to have a JEDEC parameter header and corresponding table.
#[derive(Debug, Serialize)]
pub struct SfdpPhdr {
    pub id: u8,
    pub minor: u8,
    pub major: u8,
    pub dwords: u8,
    pub offset: u32,
}

impl TryFrom<&[u8]> for SfdpPhdr {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(SfdpPhdr {
            id: reader.read_u8()?,
            minor: reader.read_u8()?,
            major: reader.read_u8()?,
            dwords: reader.read_u8()?,
            offset: reader.read_u32::<LittleEndian>()? & 0x00FFFFFFu32,
        })
    }
}

// The internal JEDEC parameter struct is used as an intermediate representation
// in creating the user-visible JEDEC parameter struct.
struct InternalJedecParams {
    pub data: Vec<u32>,
}

impl TryFrom<&[u8]> for InternalJedecParams {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut data = vec![0u32; buf.len() / 4];
        reader.read_u32_into::<LittleEndian>(&mut data)?;
        Ok(InternalJedecParams { data })
    }
}

// The JEDEC parameter table is documented in JESD216 "Serial Flash Discoverable Parameters".
// The format of the parameter table is expressed in that document as a set of bitfields
// in the various "dwords" which make up the table.
//
// We use the `field` macro to express how to extract and convert the various bitfields
// into useful values.  The macro generates a function named `ident` which extracts
// `bitsize` bits starting at `bitoffset` in the `field`th "dword" of the data.
macro_rules! field {
    // Extract to bool.
    ($name:ident -> bool, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<bool, Error> {
            Ok(BitField::new($bitoffset, $bitsize).extract(self.data[$field]) != 0)
        }
    };
    // Extract an entire u32 word.
    ($name:ident -> u32, $field:expr, 0, 32) => {
        pub fn $name(&self) -> Result<u32, Error> {
            Ok(self.data[$field])
        }
    };
    // Extract a bitfield as u32.
    ($name:ident -> u32, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<u32, Error> {
            Ok(BitField::new($bitoffset, $bitsize).extract(self.data[$field]))
        }
    };
    // Extract a bitfield as some other type.
    ($name:ident -> $type:ty, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<$type, Error> {
            Ok(<$type>::try_from(
                BitField::new($bitoffset, $bitsize).extract(self.data[$field]),
            )?)
        }
    };
}

impl InternalJedecParams {
    field!(block_erase_size -> BlockEraseSize, 0, 0, 2);
    field!(write_granularity -> WriteGranularity, 0, 2, 1);
    field!(write_en_required -> bool, 0, 3, 1);
    field!(write_en_opcode -> bool, 0, 4, 1);
    field!(erase_opcode_4kib -> u8, 0, 8, 8);
    field!(support_fast_read_112 -> bool, 0, 16, 1);
    field!(address_modes -> SupportedAddressModes, 0, 17, 2);
    field!(support_double_rate_clocking -> bool, 0, 19, 1);
    field!(support_fast_read_122 -> bool, 0, 20, 1);
    field!(support_fast_read_144 -> bool, 0, 21, 1);
    field!(support_fast_read_114 -> bool, 0, 22, 1);

    field!(density -> u32, 1, 0, 32);

    field!(wait_states_144 -> u8, 2, 0, 5);
    field!(mode_bits_144 -> u8, 2, 0, 3);
    field!(read_opcode_144 -> u8, 2, 0, 8);
    field!(wait_states_114 -> u8, 2, 16, 5);
    field!(mode_bits_114 -> u8, 2, 21, 3);
    field!(read_opcode_114 -> u8, 2, 24, 8);

    field!(wait_states_122 -> u8, 3, 0, 5);
    field!(mode_bits_122 -> u8, 3, 0, 3);
    field!(read_opcode_122 -> u8, 3, 0, 8);
    field!(wait_states_112 -> u8, 3, 16, 5);
    field!(mode_bits_112 -> u8, 3, 21, 3);
    field!(read_opcode_112 -> u8, 3, 22, 8);

    field!(support_fast_read_222 -> bool, 4, 0, 1);
    field!(support_fast_read_444 -> bool, 4, 4, 1);

    field!(wait_states_222 -> u8, 5, 16, 5);
    field!(mode_bits_222 -> u8, 5, 21, 3);
    field!(read_opcode_222 -> u8, 5, 22, 8);
    field!(wait_states_444 -> u8, 6, 16, 5);
    field!(mode_bits_444 -> u8, 6, 21, 3);
    field!(read_opcode_444 -> u8, 6, 22, 8);

    field!(sector_type1_size -> u8, 7, 0, 8);
    field!(sector_type1_opcode -> u8, 7, 8, 8);
    field!(sector_type2_size -> u8, 7, 16, 8);
    field!(sector_type2_opcode -> u8, 7, 24, 8);
    field!(sector_type3_size -> u8, 8, 0, 8);
    field!(sector_type3_opcode -> u8, 8, 8, 8);
    field!(sector_type4_size -> u8, 8, 16, 8);
    field!(sector_type4_opcode -> u8, 8, 24, 8);
}

/// `BlockEraseSize` represents whether or not the device can perform
/// a 4KiB erase.
#[derive(Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum BlockEraseSize {
    Reserved0 = 0,
    Block4KiB = 1,
    Reserved2 = 2,
    BlockNot4KiB = 3,
    #[num_enum(default)]
    Invalid,
}

impl Default for BlockEraseSize {
    fn default() -> Self {
        BlockEraseSize::Invalid
    }
}

/// `WriteGranularity` represents whether or not the device has an internal
/// buffer for program operations.
#[derive(Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum WriteGranularity {
    Granularity1Byte = 0,
    Granularity64Bytes = 1,
    #[num_enum(default)]
    Invalid,
}

impl Default for WriteGranularity {
    fn default() -> Self {
        WriteGranularity::Invalid
    }
}

/// `SupportedAddressModes` represents which addressing modes are valid for
/// the device.
#[derive(Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum SupportedAddressModes {
    Mode3b = 0,
    Mode3b4b = 1,
    Mode4b = 2,
    Reserved = 3,
    #[num_enum(default)]
    Invalid,
}

impl Default for SupportedAddressModes {
    fn default() -> Self {
        SupportedAddressModes::Invalid
    }
}

/// `FastReadParam` represents the parameters for the different styles of fast read.
#[derive(Default, Debug, Serialize)]
pub struct FastReadParam {
    pub wait_states: u8,
    pub mode_bits: u8,
    pub opcode: u8,
}

/// `Sector` represents the supported erase sector sizes of the device.
#[derive(Default, Debug, Serialize)]
pub struct Sector {
    pub size: u32,
    pub erase_opcode: u8,
}

/// The JEDEC parameter table is documented in JESD216 "Serial Flash Discoverable Parameters".
/// This structure represents the parameter table after decoding it from the packed bitfield
/// representation documented by JEDEC.
#[derive(Default, Debug, Serialize)]
pub struct JedecParams {
    /// Erase granularity.
    pub block_erase_size: BlockEraseSize,
    /// Write granularity / buffer size.
    pub write_granularity: WriteGranularity,
    /// WREN instruction required for writing to volatile status register.
    pub write_en_required: bool,
    /// Write enable opocde (this is a single bit in the jedec table; expanded
    /// to the actual opcode here).
    pub write_en_opcode: u8,
    /// Erase opcode for 4KiB sector erase.
    pub erase_opcode_4kib: u8,
    /// Support Fast Read 1-1-2.
    pub support_fast_read_112: bool,
    /// The address modes supported by the device.
    pub address_modes: SupportedAddressModes,
    /// Device supports double rate clocking.
    pub support_double_rate_clocking: bool,
    /// Other styles of Fast Read.  The numerical designator refers to
    /// the instruction transfer mode, the address transfer mode and data
    /// transfer mode.
    /// ie: 1-2-2 means single bit mode for the opcode, dual mode for the address
    /// and dual mode for the data phase.
    pub support_fast_read_122: bool,
    pub support_fast_read_144: bool,
    pub support_fast_read_114: bool,
    pub support_fast_read_222: bool,
    pub support_fast_read_444: bool,

    /// The density of the part. In the jedec table, this is expressed in bits,
    /// but it is converted to bytes here.
    pub density: u32,
    /// Parameters for the various supported FastRead modes.
    pub param_112: FastReadParam,
    pub param_122: FastReadParam,
    pub param_114: FastReadParam,
    pub param_144: FastReadParam,
    pub param_222: FastReadParam,
    pub param_444: FastReadParam,
    /// Erase sector sizes.  It is common for devices to support a 4KiB erase
    /// size, a 32KiB erase size and a 64KiB erase size.
    pub sector: [Sector; 4],
}

impl TryFrom<&[u8]> for JedecParams {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let p = InternalJedecParams::try_from(buf)?;
        let size_bytes = if p.density()? & 0x8000_0000 == 0 {
            (p.density()? + 1) / 8
        } else {
            1u32 << ((p.density()? & 0x7FFF_FFFF) - 8)
        };
        let mut jedec = JedecParams {
            block_erase_size: p.block_erase_size()?,
            write_granularity: p.write_granularity()?,
            write_en_required: p.write_en_required()?,
            write_en_opcode: if p.write_en_opcode()? { 0x50 } else { 0x06 },
            erase_opcode_4kib: p.erase_opcode_4kib()?,
            support_fast_read_112: p.support_fast_read_112()?,
            address_modes: p.address_modes()?,
            support_double_rate_clocking: p.support_double_rate_clocking()?,
            support_fast_read_122: p.support_fast_read_122()?,
            support_fast_read_144: p.support_fast_read_144()?,
            support_fast_read_114: p.support_fast_read_114()?,
            support_fast_read_222: p.support_fast_read_222()?,
            support_fast_read_444: p.support_fast_read_444()?,
            density: size_bytes,
            sector: [
                Sector {
                    size: 1u32 << p.sector_type1_size()?,
                    erase_opcode: p.sector_type1_opcode()?,
                },
                Sector {
                    size: 1u32 << p.sector_type2_size()?,
                    erase_opcode: p.sector_type2_opcode()?,
                },
                Sector {
                    size: 1u32 << p.sector_type3_size()?,
                    erase_opcode: p.sector_type3_opcode()?,
                },
                Sector {
                    size: 1u32 << p.sector_type4_size()?,
                    erase_opcode: p.sector_type4_opcode()?,
                },
            ],
            ..Default::default()
        };
        if jedec.support_fast_read_112 {
            jedec.param_112 = FastReadParam {
                wait_states: p.wait_states_112()?,
                mode_bits: p.mode_bits_112()?,
                opcode: p.read_opcode_112()?,
            }
        }
        if jedec.support_fast_read_122 {
            jedec.param_122 = FastReadParam {
                wait_states: p.wait_states_122()?,
                mode_bits: p.mode_bits_122()?,
                opcode: p.read_opcode_122()?,
            }
        }
        if jedec.support_fast_read_144 {
            jedec.param_144 = FastReadParam {
                wait_states: p.wait_states_144()?,
                mode_bits: p.mode_bits_144()?,
                opcode: p.read_opcode_144()?,
            }
        }
        if jedec.support_fast_read_114 {
            jedec.param_114 = FastReadParam {
                wait_states: p.wait_states_114()?,
                mode_bits: p.mode_bits_114()?,
                opcode: p.read_opcode_114()?,
            }
        }
        if jedec.support_fast_read_222 {
            jedec.param_222 = FastReadParam {
                wait_states: p.wait_states_222()?,
                mode_bits: p.mode_bits_222()?,
                opcode: p.read_opcode_222()?,
            }
        }
        if jedec.support_fast_read_444 {
            jedec.param_444 = FastReadParam {
                wait_states: p.wait_states_444()?,
                mode_bits: p.mode_bits_444()?,
                opcode: p.read_opcode_444()?,
            }
        }
        Ok(jedec)
    }
}

/// An `UnknownParams` structure represents SFDP parameter tables for which
/// we don't have a specialized parser.
#[derive(Debug, Serialize)]
pub struct UnknownParams {
    pub data: Vec<u32>,
}

impl TryFrom<&[u8]> for UnknownParams {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut data = vec![0u32; buf.len() / 4];
        reader.read_u32_into::<LittleEndian>(&mut data)?;
        Ok(UnknownParams { data })
    }
}

/// The `Sfdp` structure represents the decoded SFDP table.
#[derive(Debug, Serialize)]
pub struct Sfdp {
    pub header: SfdpHeader,
    pub phdr: Vec<SfdpPhdr>,
    pub jedec: JedecParams,
    pub params: Vec<UnknownParams>,
}

impl Sfdp {
    /// Given an initial SFDP buffer calculate the number of bytes needed for
    /// the entire SFDP.
    pub fn length_required(buf: &[u8]) -> Result<usize, Error> {
        if buf.len() < 256 {
            // Technically, we could read out the first 8-bytes, then
            // figure out how many phdrs there are, read out that number
            // times 8-byte chunks, then find the max extent of the pointed-to
            // headers and perform the calculation in the else-arm below.
            //
            // We punt and read out the first 256 bytes, which is often more
            // than enough.  In the event it isn't, we assume the first 256
            // bytes will contain all of the phdrs (it will) and perform
            // the max-extent calculation below.
            Ok(256)
        } else {
            let header = SfdpHeader::try_from(&buf[0..8])?;
            let mut len = 0;
            for i in 0..=header.nph {
                let start = (8 + i * 8) as usize;
                let end = start + 8;
                let phdr = SfdpPhdr::try_from(&buf[start..end])?;
                len = std::cmp::max(len, phdr.offset + (phdr.dwords * 4) as u32);
                log::debug!("computed sfdp len = {}", len);
            }
            Ok(len as usize)
        }
    }
}

/// Convert a byte buffer into an SFDP structure.
impl TryFrom<&[u8]> for Sfdp {
    type Error = anyhow::Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let header = SfdpHeader::try_from(buf.get(0..8).ok_or(Error::SliceRange(0, 8))?)?;
        let mut phdr = Vec::new();
        for i in 0..=header.nph {
            let start = (8 + i * 8) as usize;
            let end = start + 8;
            phdr.push(SfdpPhdr::try_from(
                buf.get(start..end).ok_or(Error::SliceRange(start, end))?,
            )?);
        }

        let start = phdr[0].offset as usize;
        let end = start + phdr[0].dwords as usize * 4;
        let jedec =
            JedecParams::try_from(buf.get(start..end).ok_or(Error::SliceRange(start, end))?)?;

        let mut params = Vec::new();
        for ph in phdr.iter().take((header.nph as usize) + 1).skip(1) {
            let start = ph.offset as usize;
            let end = start + ph.dwords as usize * 4;
            params.push(UnknownParams::try_from(
                buf.get(start..end).ok_or(Error::SliceRange(start, end))?,
            )?);
        }

        Ok(Sfdp {
            header,
            phdr,
            jedec,
            params,
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;

    #[rustfmt::skip]
    const SFDP_MX66L1G: &[u8; 512] = include_bytes!("SFDP_MX66L1G.bin");

    #[allow(clippy::bool_assert_comparison)]
    #[test]
    fn test_decode_mx66l1g() -> Result<()> {
        let sfdp = Sfdp::try_from(&SFDP_MX66L1G[..])?;
        // A simple spot-check of values from the SFDP table.
        assert_eq!(sfdp.header.signature, 0x50444653);
        assert_eq!(sfdp.header.major, 1);
        assert_eq!(sfdp.header.minor, 6);
        assert_eq!(sfdp.header.nph, 2);

        assert_eq!(sfdp.jedec.block_erase_size, BlockEraseSize::Block4KiB);
        assert_eq!(sfdp.jedec.write_en_required, false);
        assert_eq!(sfdp.jedec.write_en_opcode, 0x06);
        assert_eq!(sfdp.jedec.erase_opcode_4kib, 0x20);
        assert_eq!(sfdp.jedec.support_fast_read_112, true);
        assert_eq!(sfdp.jedec.address_modes, SupportedAddressModes::Mode3b4b);
        assert_eq!(sfdp.jedec.density, 128 * 1024 * 1024);
        Ok(())
    }

    // Regression test for https://github.com/lowRISC/opentitan/issues/13477
    #[test]
    fn test_bad_header_signature() -> Result<()> {
        let buf = &[255u8; 256];
        let sfdp = Sfdp::try_from(&buf[..]);
        assert!(sfdp.is_err());
        let err = sfdp.unwrap_err();
        assert_eq!(
            err.to_string(),
            "SFDP header contains incorrect signature: 0xffffffff"
        );
        Ok(())
    }
}
