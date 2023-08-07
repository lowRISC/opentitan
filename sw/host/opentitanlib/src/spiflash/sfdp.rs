// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use byteorder::{LittleEndian, ReadBytesExt};
use num_enum::FromPrimitive;
use serde::Serialize;
use serde_annotate::Annotate;
use std::convert::TryFrom;
use std::time::Duration;
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
#[derive(Debug, Serialize, Annotate)]
pub struct SfdpHeader {
    #[annotate(format=hex, comment=comment_signature())]
    pub signature: u32,
    #[annotate(comment=comment_version())]
    pub minor: u8,
    pub major: u8,
    #[annotate(comment = "Number of parameter headers minus one")]
    pub nph: u8,
    #[annotate(format=bin, comment="The reserved field should be all ones")]
    pub reserved: u8,
}

impl SfdpHeader {
    fn comment_signature(&self) -> Option<String> {
        let signature = self.signature.to_le_bytes().map(|b| {
            match b {
                // The ASCII printable range is [0x20, 0x7E].
                0x20..=0x7E => b as char,
                _ => '.',
            }
        });
        Some(format!(
            "Signature value='{}{}{}{}' (should be 'SFDP')",
            signature[0], signature[1], signature[2], signature[3],
        ))
    }
    fn comment_version(&self) -> Option<String> {
        Some(format!("{}.{}", self.major, self.minor))
    }
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
//
// Since the documentation for dword offsets is 1-based, the marco parameter `field`
// is also 1-based.
macro_rules! field {
    // Extract to bool.
    ($name:ident -> bool, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<bool, Error> {
            Ok(BitField::new($bitoffset, $bitsize).extract(self.data[$field - 1]) != 0)
        }
    };
    // Extract an entire u32 word.
    ($name:ident -> u32, $field:expr, 0, 32) => {
        pub fn $name(&self) -> Result<u32, Error> {
            Ok(self.data[$field - 1])
        }
    };
    // Extract a bitfield as u32.
    ($name:ident -> u32, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<u32, Error> {
            Ok(BitField::new($bitoffset, $bitsize).extract(self.data[$field - 1]))
        }
    };
    // Extract a bitfield as some other type.
    ($name:ident -> $type:ty, $field:expr, $bitoffset:expr, $bitsize:expr) => {
        pub fn $name(&self) -> Result<$type, Error> {
            Ok(<$type>::try_from(
                BitField::new($bitoffset, $bitsize).extract(self.data[$field - 1]),
            )?)
        }
    };
}

impl InternalJedecParams {
    field!(block_erase_size -> BlockEraseSize, 1, 0, 2);
    field!(write_granularity -> WriteGranularity, 1, 2, 1);
    field!(write_en_required -> bool, 1, 3, 1);
    field!(write_en_opcode -> bool, 1, 4, 1);
    field!(erase_opcode_4kib -> u8, 1, 8, 8);
    field!(support_fast_read_112 -> bool, 1, 16, 1);
    field!(address_modes -> SupportedAddressModes, 1, 17, 2);
    field!(support_double_rate_clocking -> bool, 1, 19, 1);
    field!(support_fast_read_122 -> bool, 1, 20, 1);
    field!(support_fast_read_144 -> bool, 1, 21, 1);
    field!(support_fast_read_114 -> bool, 1, 22, 1);

    field!(density -> u32, 2, 0, 31);
    field!(density_pow2 -> bool, 2, 31, 1);

    field!(wait_states_144 -> u8, 3, 0, 5);
    field!(mode_bits_144 -> u8, 3, 5, 3);
    field!(read_opcode_144 -> u8, 3, 8, 8);
    field!(wait_states_114 -> u8, 3, 16, 5);
    field!(mode_bits_114 -> u8, 3, 21, 3);
    field!(read_opcode_114 -> u8, 3, 24, 8);

    field!(wait_states_112 -> u8, 4, 0, 5);
    field!(mode_bits_112 -> u8, 4, 5, 3);
    field!(read_opcode_112 -> u8, 4, 8, 8);
    field!(wait_states_122 -> u8, 4, 16, 5);
    field!(mode_bits_122 -> u8, 4, 21, 3);
    field!(read_opcode_122 -> u8, 4, 24, 8);

    field!(support_fast_read_222 -> bool, 5, 0, 1);
    field!(support_fast_read_444 -> bool, 5, 4, 1);

    field!(wait_states_222 -> u8, 6, 16, 5);
    field!(mode_bits_222 -> u8, 6, 21, 3);
    field!(read_opcode_222 -> u8, 6, 24, 8);

    field!(wait_states_444 -> u8, 7, 16, 5);
    field!(mode_bits_444 -> u8, 7, 21, 3);
    field!(read_opcode_444 -> u8, 7, 24, 8);

    field!(sector_type1_size -> u8, 8, 0, 8);
    field!(sector_type1_opcode -> u8, 8, 8, 8);
    field!(sector_type2_size -> u8, 8, 16, 8);
    field!(sector_type2_opcode -> u8, 8, 24, 8);

    field!(sector_type3_size -> u8, 9, 0, 8);
    field!(sector_type3_opcode -> u8, 9, 8, 8);
    field!(sector_type4_size -> u8, 9, 16, 8);
    field!(sector_type4_opcode -> u8, 9, 24, 8);

    // JESD216B pp. 20-21.
    field!(erase_time_multiplier -> u32, 10, 0, 4);
    field!(erase_type1_time -> u32, 10, 4, 5);
    field!(erase_type1_unit -> usize, 10, 9, 2);
    field!(erase_type2_time -> u32, 10, 11, 5);
    field!(erase_type2_unit -> usize, 10, 16, 2);
    field!(erase_type3_time -> u32, 10, 18, 5);
    field!(erase_type3_unit -> usize, 10, 23, 2);
    field!(erase_type4_time -> u32, 10, 25, 5);
    field!(erase_type4_unit -> usize, 10, 30, 2);

    // JESD216B pg. 22.
    field!(pgm_time_multiplier -> u32, 11, 0, 4);
    field!(page_size -> u32, 11, 4, 4);
    field!(page_pgm_time -> u32, 11, 8, 5);
    field!(page_pgm_unit -> usize, 11, 13, 1);
    field!(byte_pgm_time -> u32, 11, 14, 4);
    field!(byte_pgm_unit -> usize, 11, 18, 1);
    field!(additional_byte_pgm_time -> u32, 11, 19, 4);
    field!(additional_byte_pgm_unit -> usize, 11, 23, 1);
    field!(chip_erase_time -> u32, 11, 24, 5);
    field!(chip_erase_unit -> usize, 11, 29, 2);

    // JESD216B pp. 23-24.
    field!(prohibited_pgm_suspend -> u8, 12, 0, 4);
    field!(prohibited_erase_suspend -> u8, 12, 4, 4);
    field!(pgm_resume_to_suspend -> u32, 12, 9, 4);
    field!(suspend_pgm_latency_time -> u32, 12, 13, 5);
    field!(suspend_pgm_latency_unit -> usize, 12, 18, 2);
    field!(erase_resume_to_suspend -> u32, 12, 20, 4);
    field!(suspend_erase_latency_time -> u32, 12, 24, 5);
    field!(suspend_erase_latency_unit -> usize, 12, 29, 2);
    field!(suspend_resume_supported -> bool, 12, 31, 1);

    // JESD216B pg. 25.
    field!(pgm_resume_instruction -> u8, 13, 0, 8);
    field!(pgm_suspend_instruction -> u8, 13, 8, 8);
    field!(resume_instruction -> u8, 13, 16, 8);
    field!(suspend_instruction -> u8, 13, 24, 8);

    // JESD216B pg. 25.
    field!(status_busy_polling -> u8, 14, 2, 6);
    field!(exit_deep_powerdown_time -> u32, 14, 8, 5);
    field!(exit_deep_powerdown_unit -> usize, 14, 13, 2);
    field!(exit_deep_powerdown_instruction -> u8, 14, 15, 8);
    field!(enter_deep_powerdown_instruction -> u8, 14, 23, 8);
    field!(deep_powerdown_supported -> bool, 14, 31, 1);

    // JESD216B pp. 26-27.
    field!(mode_444_disable -> u8, 15, 0, 4);
    field!(mode_444_enable -> u8, 15, 4, 5);
    field!(mode_444_supported -> bool, 15, 9, 1);
    field!(mode_444_exit -> u8, 15, 10, 6);
    field!(mode_444_entry -> u8, 15, 16, 4);
    field!(quad_enable_requirements -> u8, 15, 20, 3);
    field!(hold_or_reset_disable -> bool, 15, 23, 1);

    // JESD216B pp. 28-29.
    field!(status_reg1_write_enable -> u8, 16, 0, 6);
    field!(soft_reset_support -> u8, 16, 8, 6);
    field!(exit_4b_addressing -> u16, 16, 14, 10);
    field!(enter_4b_addressing -> u8, 16, 24, 8);

    // JESD216D.01 pg. 44.
    field!(wait_states_188 -> u8, 17, 0, 5);
    field!(mode_bits_188 -> u8, 17, 5, 3);
    field!(read_opcode_188 -> u8, 17, 8, 8);
    field!(wait_states_118 -> u8, 17, 16, 5);
    field!(mode_bits_118 -> u8, 17, 21, 3);
    field!(read_opcode_118 -> u8, 17, 24, 8);

    // JESD216D.01 pg. 45.
    field!(output_driver_strength -> u8, 18, 18, 5);
    field!(spi_protocol_reset -> bool, 18, 23, 1);
    field!(data_strobe_str -> u8, 18, 24, 2);
    field!(data_qpi_str -> bool, 18, 26, 1);
    field!(data_qpi_dtr -> bool, 18, 27, 1);
    field!(octal_dtr_command -> u8, 18, 29, 2);
    field!(octal_byte_order -> u8, 18, 31, 1);

    // JESD216D.01 pg. 48.
    field!(mode_8s8s8s_disable-> u8, 19, 0, 4);
    field!(mode_8s8s8s_enable-> u8, 19, 4, 5);
    field!(mode_088_supported -> bool, 19, 9, 1);
    field!(mode_088_exit -> u8, 19, 10, 6);
    field!(mode_088_enter -> u8, 19, 16, 4);
    field!(octal_enable_requirements -> u8, 19, 20, 3);

    // JESD216D.01 pp. 49-51.
    field!(max_speed_4s4s4s_no_strobe -> MaxSpeed, 20, 0, 4);
    field!(max_speed_4s4s4s_strobe    -> MaxSpeed, 20, 4, 4);
    field!(max_speed_4d4d4d_no_strobe -> MaxSpeed, 20, 8, 4);
    field!(max_speed_4d4d4d_strobe    -> MaxSpeed, 20, 12, 4);
    field!(max_speed_8s8s8s_no_strobe -> MaxSpeed, 20, 16, 4);
    field!(max_speed_8s8s8s_strobe    -> MaxSpeed, 20, 20, 4);
    field!(max_speed_8d8d8d_no_strobe -> MaxSpeed, 20, 24, 4);
    field!(max_speed_8d8d8d_strobe    -> MaxSpeed, 20, 28, 4);

    // JESD216F.01 pg. 52.
    field!(support_fast_read_1s1d1d -> bool, 21, 0, 1);
    field!(support_fast_read_1s2d2d -> bool, 21, 1, 1);
    field!(support_fast_read_1s4d4d -> bool, 21, 2, 1);
    field!(support_fast_read_4s4d4d -> bool, 21, 3, 1);

    // JESD216F.01 pg. 53.
    field!(wait_states_1s1d1d -> u8, 22, 0, 5);
    field!(mode_bits_1s1d1d   -> u8, 22, 5, 3);
    field!(read_opcode_1s1d1d -> u8, 22, 8, 8);
    field!(wait_states_1s2d2d -> u8, 22, 16, 5);
    field!(mode_bits_1s2d2d   -> u8, 22, 21, 3);
    field!(read_opcode_1s2d2d -> u8, 22, 24, 8);

    // JESD216F.01 pg. 54.
    field!(wait_states_1s4d4d -> u8, 23, 0, 5);
    field!(mode_bits_1s4d4d   -> u8, 23, 5, 3);
    field!(read_opcode_1s4d4d -> u8, 23, 8, 8);
    field!(wait_states_4s4d4d -> u8, 23, 16, 5);
    field!(mode_bits_4s4d4d   -> u8, 23, 21, 3);
    field!(read_opcode_4s4d4d -> u8, 23, 24, 8);
}

/// `BlockEraseSize` represents whether or not the device can perform
/// a 4KiB erase.
#[derive(Default, Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum BlockEraseSize {
    Reserved0 = 0,
    Block4KiB = 1,
    Reserved2 = 2,
    BlockNot4KiB = 3,
    #[default]
    Invalid,
}

/// `WriteGranularity` represents whether or not the device has an internal
/// buffer for program operations.
#[derive(Default, Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum WriteGranularity {
    Granularity1Byte = 0,
    Granularity64Bytes = 1,
    #[default]
    Invalid,
}

/// `SupportedAddressModes` represents which addressing modes are valid for
/// the device.
#[derive(Default, Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum SupportedAddressModes {
    Mode3b = 0,
    Mode3b4b = 1,
    Mode4b = 2,
    Reserved = 3,
    #[default]
    Invalid,
}

#[derive(Default, Debug, Eq, PartialEq, FromPrimitive, Clone, Copy, Serialize)]
#[repr(u32)]
pub enum MaxSpeed {
    Reserved0 = 0,
    Speed33MHz,
    Speed50MHz,
    Speed66MHz,
    Speed80MHz,
    Speed100MHz,
    Speed133MHz,
    Speed166MHz,
    Speed200MHz,
    Speed250MHz,
    Speed266MHz,
    Speed333MHz,
    Speed400MHz,
    Reserved10,
    NotCharacterized,
    #[default]
    NotSupported,
}

/// `FastReadParam` represents the parameters for the different styles of fast read.
#[derive(Clone, Default, Debug, Serialize, Annotate)]
pub struct FastReadParam {
    pub wait_states: u8,
    pub mode_bits: u8,
    #[annotate(format=hex)]
    pub opcode: u8,
}

/// `SectorErase` represents the supported erase sector sizes of the device.
#[derive(Clone, Default, Debug, Serialize, Annotate)]
pub struct SectorErase {
    pub size: u32,
    #[annotate(format=hex)]
    pub opcode: u8,
    pub time: Option<TimeBound>,
}

#[derive(Clone, Default, Debug, Serialize)]
pub struct TimeBound {
    #[serde(with = "humantime_serde")]
    pub typical: Duration,
    #[serde(with = "humantime_serde")]
    pub maximum: Duration,
}

/// The JEDEC parameter table is documented in JESD216 "Serial Flash Discoverable Parameters".
/// This structure represents the parameter table after decoding it from the packed bitfield
/// representation documented by JEDEC.
///
/// I have access to the following specs:
/// - JESD216 dated April 2011 (Flash parameters version 1.0).
/// - JESD216B dated May 2014 (Flash parameters version 1.6).
/// - JESD216D dated August 2019 (Flash parameters version 1.7, unchanged since rev C).
/// - JESD216F dated February 2022 (Flash parameters version 1.7, unchanged since rev D).
///
/// - Version 1.0 defines a table of 9 "dwords". I'm considering this to be the
///   minimum required parameter table.
/// - Rev B, version 1.6 extends the table to 16 "dwords", including information about
///   erase timing, powerdown and alternate mode requirements.
/// - Rev D, version 1.7 extends the table to 20 "dwords", including information about
///   eight-lane SPI modes.
/// - Rev F, version 1.7 extends the table to 23 "dwords", including information about
///   dual data rate operations.
#[derive(Default, Debug, Serialize, Annotate)]
pub struct JedecParams {
    /// Erase granularity.
    pub block_erase_size: BlockEraseSize,
    /// Write granularity / buffer size.
    pub write_granularity: WriteGranularity,
    /// WREN instruction required for writing to volatile status register.
    pub write_en_required: bool,
    /// Write enable opocde (this is a single bit in the jedec table; expanded
    /// to the actual opcode here).
    #[annotate(format=hex)]
    pub write_en_opcode: u8,
    /// Erase opcode for 4KiB sector erase.
    #[annotate(format=hex)]
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
    pub erase: [SectorErase; 4],

    // TODO: Get ahold of Revs A, C & E and restructure the revision extensions.
    pub rev_b: Option<JedecParamsRevB>,
    pub rev_d: Option<JedecParamsRevD>,
    pub rev_f: Option<JedecParamsRevF>,
}

/// The Rev B extensions to the JEDEC parameters table.
#[derive(Default, Debug, Serialize, Annotate)]
pub struct JedecParamsRevB {
    pub page_size: u32,
    pub page_program_time: TimeBound,
    pub byte_program_time: TimeBound,
    pub additional_byte_program_time: TimeBound,
    pub chip_erase_time: TimeBound,

    pub suspend_resume_supported: bool,
    pub prohibited_ops_program_suspend: u8,
    pub prohibited_ops_erase_suspend: u8,
    #[serde(with = "humantime_serde")]
    pub program_resume_to_suspend: Duration,
    #[serde(with = "humantime_serde")]
    pub suspend_in_progress_program_latency: Duration,
    #[serde(with = "humantime_serde")]
    pub erase_resume_to_suspend: Duration,
    #[serde(with = "humantime_serde")]
    pub suspend_in_progress_erase_latency: Duration,
    #[annotate(format=hex)]
    pub program_resume_instruction: u8,
    #[annotate(format=hex)]
    pub program_suspend_instruction: u8,
    #[annotate(format=hex)]
    pub resume_instruction: u8,
    #[annotate(format=hex)]
    pub suspend_instruction: u8,

    pub deep_powerdown_supported: bool,
    #[annotate(format=hex)]
    pub enter_deep_powerdown_instruction: u8,
    #[annotate(format=hex)]
    pub exit_deep_powerdown_instruction: u8,
    #[serde(with = "humantime_serde")]
    pub exit_deep_powerdown_delay: Duration,
    pub status_register_polling: u8,

    pub hold_or_reset_disable: bool,
    pub quad_enable_requirements: u8,
    pub mode_444_entry: u8,
    pub mode_444_exit: u8,
    pub mode_444_supported: bool,
    pub mode_444_disable: u8,
    pub mode_444_enable: u8,

    pub enter_4b_addressing: u8,
    pub exit_4b_addressing: u16,
    pub soft_reset_support: u8,
    pub status_reg1_write_enable: u8,
}

/// The Rev D extensions to the JEDEC parameters table.
#[derive(Default, Debug, Serialize)]
pub struct JedecParamsRevD {
    pub param_118: FastReadParam,
    pub param_188: FastReadParam,

    pub output_driver_strength: u8,
    pub jedec_spi_protocol_reset: bool,
    pub data_strobe_waveform_str: u8,
    pub data_strobe_support_4s4s4s: bool,
    pub data_strobe_support_4d4d4d: bool,
    pub octal_dtr_command: u8,
    pub octal_byte_order: u8,

    pub mode_8s8s8s_disable: u8,
    pub mode_8s8s8s_enable: u8,
    pub mode_088_supported: bool,
    pub mode_088_exit: u8,
    pub mode_088_enter: u8,
    pub octal_enable_requirements: u8,

    pub max_speed_4s4s4s_no_strobe: MaxSpeed,
    pub max_speed_4s4s4s_strobe: MaxSpeed,
    pub max_speed_4d4d4d_no_strobe: MaxSpeed,
    pub max_speed_4d4d4d_strobe: MaxSpeed,
    pub max_speed_8s8s8s_no_strobe: MaxSpeed,
    pub max_speed_8s8s8s_strobe: MaxSpeed,
    pub max_speed_8d8d8d_no_strobe: MaxSpeed,
    pub max_speed_8d8d8d_strobe: MaxSpeed,
}

/// The Rev F extensions to the JEDEC parameters table.
#[derive(Default, Debug, Serialize)]
pub struct JedecParamsRevF {
    pub param_1s1d1d: Option<FastReadParam>,
    pub param_1s2d2d: Option<FastReadParam>,
    pub param_1s4d4d: Option<FastReadParam>,
    pub param_4s4d4d: Option<FastReadParam>,
}

impl JedecParams {
    // JESD216B section 6.4.13 (pg. 20)
    const ERASE_TIME_UNITS: [Duration; 4] = [
        Duration::from_millis(1),
        Duration::from_millis(16),
        Duration::from_millis(128),
        Duration::from_secs(1),
    ];
    // JESD216B section 6.4.14 (pg. 22)
    const CHIP_ERASE_UNITS: [Duration; 4] = [
        Duration::from_millis(16),
        Duration::from_millis(256),
        Duration::from_secs(4),
        Duration::from_secs(64),
    ];
    // JESD216B section 6.4.14 (pg. 22)
    const PAGE_PGM_UNITS: [Duration; 2] = [Duration::from_micros(8), Duration::from_micros(64)];
    // JESD216B section 6.4.14 (pg. 22)
    const BYTE_PGM_UNITS: [Duration; 2] = [Duration::from_micros(1), Duration::from_micros(8)];
    // JESD216B section 6.4.15 (pg. 23)
    const SUSPEND_RESUME_UNITS: [Duration; 4] = [
        Duration::from_nanos(128),
        Duration::from_micros(1),
        Duration::from_micros(8),
        Duration::from_micros(64),
    ];

    fn pow2_size(shift: u8) -> u32 {
        if shift == 0 {
            0
        } else {
            1u32 << shift
        }
    }
}

impl TryFrom<&[u8]> for JedecParams {
    type Error = Error;
    fn try_from(buf: &[u8]) -> Result<Self, Self::Error> {
        let p = InternalJedecParams::try_from(buf)?;
        let size_bytes = if p.density_pow2()? {
            1u32 << ((p.density()? & 0x7FFF_FFFF) - 8)
        } else {
            (p.density()? + 1) / 8
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
            erase: [
                SectorErase {
                    size: Self::pow2_size(p.sector_type1_size()?),
                    opcode: p.sector_type1_opcode()?,
                    time: None,
                },
                SectorErase {
                    size: Self::pow2_size(p.sector_type2_size()?),
                    opcode: p.sector_type2_opcode()?,
                    time: None,
                },
                SectorErase {
                    size: Self::pow2_size(p.sector_type3_size()?),
                    opcode: p.sector_type3_opcode()?,
                    time: None,
                },
                SectorErase {
                    size: Self::pow2_size(p.sector_type4_size()?),
                    opcode: p.sector_type4_opcode()?,
                    time: None,
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
        if p.data.len() >= 16 {
            let mult = 2 * (p.erase_time_multiplier()? + 1);
            let type1 = Self::ERASE_TIME_UNITS[p.erase_type1_unit()?] * (p.erase_type1_time()? + 1);
            let type2 = Self::ERASE_TIME_UNITS[p.erase_type2_unit()?] * (p.erase_type2_time()? + 1);
            let type3 = Self::ERASE_TIME_UNITS[p.erase_type3_unit()?] * (p.erase_type3_time()? + 1);
            let type4 = Self::ERASE_TIME_UNITS[p.erase_type4_unit()?] * (p.erase_type4_time()? + 1);
            jedec.erase[0].time = Some(TimeBound {
                typical: type1,
                maximum: type1 * mult,
            });
            jedec.erase[1].time = Some(TimeBound {
                typical: type2,
                maximum: type2 * mult,
            });
            jedec.erase[2].time = Some(TimeBound {
                typical: type3,
                maximum: type3 * mult,
            });
            jedec.erase[3].time = Some(TimeBound {
                typical: type4,
                maximum: type4 * mult,
            });

            let mult = 2 * (p.pgm_time_multiplier()? + 1);
            let chip_erase_unit = Self::CHIP_ERASE_UNITS[p.chip_erase_unit()?];
            let page_pgm_unit = Self::PAGE_PGM_UNITS[p.page_pgm_unit()?];
            let byte_pgm_unit = Self::BYTE_PGM_UNITS[p.byte_pgm_unit()?];
            let additional_byte_pgm_unit = Self::BYTE_PGM_UNITS[p.additional_byte_pgm_unit()?];

            jedec.rev_b = Some(JedecParamsRevB {
                page_size: 1u32 << p.page_size()?,
                page_program_time: TimeBound {
                    typical: page_pgm_unit * (1 + p.page_pgm_time()?),
                    maximum: page_pgm_unit * (1 + p.page_pgm_time()?) * mult,
                },
                byte_program_time: TimeBound {
                    typical: byte_pgm_unit * (1 + p.byte_pgm_time()?),
                    maximum: byte_pgm_unit * (1 + p.byte_pgm_time()?) * mult,
                },
                additional_byte_program_time: TimeBound {
                    typical: additional_byte_pgm_unit * (1 + p.additional_byte_pgm_time()?),
                    maximum: additional_byte_pgm_unit * (1 + p.additional_byte_pgm_time()?) * mult,
                },
                chip_erase_time: TimeBound {
                    typical: chip_erase_unit * (1 + p.chip_erase_time()?),
                    maximum: chip_erase_unit * (1 + p.chip_erase_time()?) * mult,
                },

                suspend_resume_supported: !p.suspend_resume_supported()?,
                prohibited_ops_program_suspend: p.prohibited_pgm_suspend()?,
                prohibited_ops_erase_suspend: p.prohibited_erase_suspend()?,
                program_resume_to_suspend: Duration::from_millis(64)
                    * (1 + p.pgm_resume_to_suspend()?),
                suspend_in_progress_program_latency: Self::SUSPEND_RESUME_UNITS
                    [p.suspend_pgm_latency_unit()?]
                    * (1 + p.suspend_pgm_latency_time()?),
                erase_resume_to_suspend: Duration::from_millis(64)
                    * (1 + p.erase_resume_to_suspend()?),
                suspend_in_progress_erase_latency: Self::SUSPEND_RESUME_UNITS
                    [p.suspend_erase_latency_unit()?]
                    * (1 + p.suspend_erase_latency_time()?),
                program_resume_instruction: p.pgm_resume_instruction()?,
                program_suspend_instruction: p.pgm_suspend_instruction()?,
                resume_instruction: p.suspend_instruction()?,
                suspend_instruction: p.resume_instruction()?,

                deep_powerdown_supported: !p.deep_powerdown_supported()?,
                enter_deep_powerdown_instruction: p.enter_deep_powerdown_instruction()?,
                exit_deep_powerdown_instruction: p.exit_deep_powerdown_instruction()?,
                exit_deep_powerdown_delay: Self::SUSPEND_RESUME_UNITS
                    [p.exit_deep_powerdown_unit()?]
                    * (1 + p.exit_deep_powerdown_time()?),
                status_register_polling: p.status_busy_polling()?,

                hold_or_reset_disable: p.hold_or_reset_disable()?,
                quad_enable_requirements: p.quad_enable_requirements()?,
                mode_444_entry: p.mode_444_entry()?,
                mode_444_exit: p.mode_444_exit()?,
                mode_444_supported: p.mode_444_supported()?,
                mode_444_disable: p.mode_444_disable()?,
                mode_444_enable: p.mode_444_enable()?,

                enter_4b_addressing: p.enter_4b_addressing()?,
                exit_4b_addressing: p.exit_4b_addressing()?,
                soft_reset_support: p.soft_reset_support()?,
                status_reg1_write_enable: p.status_reg1_write_enable()?,
            });
        }
        if p.data.len() >= 20 {
            jedec.rev_d = Some(JedecParamsRevD {
                param_118: FastReadParam {
                    wait_states: p.wait_states_118()?,
                    mode_bits: p.mode_bits_118()?,
                    opcode: p.read_opcode_118()?,
                },
                param_188: FastReadParam {
                    wait_states: p.wait_states_188()?,
                    mode_bits: p.mode_bits_188()?,
                    opcode: p.read_opcode_188()?,
                },

                output_driver_strength: p.output_driver_strength()?,
                jedec_spi_protocol_reset: p.spi_protocol_reset()?,
                data_strobe_waveform_str: p.data_strobe_str()?,
                data_strobe_support_4s4s4s: p.data_qpi_str()?,
                data_strobe_support_4d4d4d: p.data_qpi_dtr()?,
                octal_dtr_command: p.octal_dtr_command()?,
                octal_byte_order: p.octal_byte_order()?,

                mode_8s8s8s_disable: p.mode_8s8s8s_disable()?,
                mode_8s8s8s_enable: p.mode_8s8s8s_enable()?,
                mode_088_supported: p.mode_088_supported()?,
                mode_088_exit: p.mode_088_exit()?,
                mode_088_enter: p.mode_088_enter()?,
                octal_enable_requirements: p.octal_enable_requirements()?,

                max_speed_4s4s4s_no_strobe: p.max_speed_4s4s4s_no_strobe()?,
                max_speed_4s4s4s_strobe: p.max_speed_4s4s4s_strobe()?,
                max_speed_4d4d4d_no_strobe: p.max_speed_4d4d4d_no_strobe()?,
                max_speed_4d4d4d_strobe: p.max_speed_4d4d4d_strobe()?,
                max_speed_8s8s8s_no_strobe: p.max_speed_8s8s8s_no_strobe()?,
                max_speed_8s8s8s_strobe: p.max_speed_8s8s8s_strobe()?,
                max_speed_8d8d8d_no_strobe: p.max_speed_8d8d8d_no_strobe()?,
                max_speed_8d8d8d_strobe: p.max_speed_8d8d8d_strobe()?,
            });
        }
        if p.data.len() >= 23 {
            let mut rev_f = JedecParamsRevF::default();
            if p.support_fast_read_1s1d1d()? {
                rev_f.param_1s1d1d = Some(FastReadParam {
                    wait_states: p.wait_states_1s1d1d()?,
                    mode_bits: p.mode_bits_1s1d1d()?,
                    opcode: p.read_opcode_1s1d1d()?,
                });
            }
            if p.support_fast_read_1s2d2d()? {
                rev_f.param_1s2d2d = Some(FastReadParam {
                    wait_states: p.wait_states_1s2d2d()?,
                    mode_bits: p.mode_bits_1s2d2d()?,
                    opcode: p.read_opcode_1s2d2d()?,
                });
            }
            if p.support_fast_read_1s4d4d()? {
                rev_f.param_1s4d4d = Some(FastReadParam {
                    wait_states: p.wait_states_1s4d4d()?,
                    mode_bits: p.mode_bits_1s4d4d()?,
                    opcode: p.read_opcode_1s4d4d()?,
                });
            }
            if p.support_fast_read_4s4d4d()? {
                rev_f.param_4s4d4d = Some(FastReadParam {
                    wait_states: p.wait_states_4s4d4d()?,
                    mode_bits: p.mode_bits_4s4d4d()?,
                    opcode: p.read_opcode_4s4d4d()?,
                });
            }
            jedec.rev_f = Some(rev_f);
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
    use humantime::parse_duration;

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

        assert_eq!(sfdp.jedec.erase[0].size, 4096);
        assert_eq!(sfdp.jedec.erase[0].opcode, 0x20);
        // The datasheet says typ=30ms, max=400ms.  The SFDP-reported
        // erase timings are advisory, have a limited representations
        // and won't match the data sheet exactly.
        assert_eq!(
            sfdp.jedec.erase[0].time.as_ref().unwrap().typical,
            parse_duration("30ms")?
        );
        assert_eq!(
            sfdp.jedec.erase[0].time.as_ref().unwrap().maximum,
            parse_duration("420ms")?
        );

        assert_eq!(sfdp.jedec.erase[1].size, 32768);
        assert_eq!(sfdp.jedec.erase[1].opcode, 0x52);
        // The datasheet says typ=0.15s, max=1s.
        assert_eq!(
            sfdp.jedec.erase[1].time.as_ref().unwrap().typical,
            parse_duration("160ms")?
        );
        assert_eq!(
            sfdp.jedec.erase[1].time.as_ref().unwrap().maximum,
            parse_duration("2s 240ms")?
        );

        assert_eq!(sfdp.jedec.erase[2].size, 65536);
        assert_eq!(sfdp.jedec.erase[2].opcode, 0xd8);
        // The datasheet says typ=0.28s, max=2s.
        assert_eq!(
            sfdp.jedec.erase[2].time.as_ref().unwrap().typical,
            parse_duration("288ms")?
        );
        assert_eq!(
            sfdp.jedec.erase[2].time.as_ref().unwrap().maximum,
            parse_duration("4s 32ms")?
        );

        assert_eq!(sfdp.jedec.erase[3].size, 0);
        assert_eq!(sfdp.jedec.erase[3].opcode, 0xff);

        let rev_b = sfdp.jedec.rev_b.as_ref().expect("rev_b parameters");
        assert_eq!(rev_b.page_size, 256);
        // The datasheet says typ=0.25ms, max=3ms.
        assert_eq!(rev_b.page_program_time.typical, parse_duration("256us")?);
        assert_eq!(rev_b.page_program_time.maximum, parse_duration("3ms 72us")?);
        // The datasheet says typ=25us, max=60us.
        assert_eq!(rev_b.byte_program_time.typical, parse_duration("32us")?);
        assert_eq!(rev_b.byte_program_time.maximum, parse_duration("384us")?);
        // The datasheet doesn't mention the additional byte programming time.
        assert_eq!(
            rev_b.additional_byte_program_time.typical,
            parse_duration("1us")?
        );
        assert_eq!(
            rev_b.additional_byte_program_time.maximum,
            parse_duration("12us")?
        );
        // The datasheet says typ=200s, max=600s. The typical time is the closest
        // possible representation given the range and units available in the SFDP.
        assert_eq!(rev_b.chip_erase_time.typical, parse_duration("4m 16s")?);
        assert_eq!(rev_b.chip_erase_time.maximum, parse_duration("51m 12s")?);

        // The particular MX66L1G sampled doesn't have a RevD or RevF table.
        assert!(sfdp.jedec.rev_d.is_none());
        assert!(sfdp.jedec.rev_f.is_none());
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
