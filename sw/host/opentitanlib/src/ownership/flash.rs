// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};

use super::misc::{TlvHeader, TlvTag};
use super::GlobalFlags;
use crate::chip::boolean::MultiBitBool4;

/// Describes the proprerties of a flash region.
#[derive(Debug, Default, Clone, Copy, Serialize, Deserialize, Annotate)]
pub struct FlashFlags {
    /// Read operations are allowed in this region.
    #[serde(default)]
    pub read: bool,
    /// Program operations are allowed in this region.
    #[serde(default)]
    pub program: bool,
    /// Erase operations are allowed in this region.
    #[serde(default)]
    pub erase: bool,
    /// Scrambling is enabled in this region.
    #[serde(default)]
    pub scramble: bool,
    /// ECC memory correction is enabled in this region.
    #[serde(default)]
    pub ecc: bool,
    /// The high endurance feature is enabled in this region.
    #[serde(default)]
    pub high_endurance: bool,
    /// Forbid program and erase operations when in the primary flash side.
    #[serde(default)]
    pub protect_when_primary: bool,
    /// Lock the configuration of this region.
    #[serde(default)]
    pub lock: bool,
}

impl FlashFlags {
    const TRUE: u64 = MultiBitBool4::True.0 as u64;
    const FALSE: u64 = MultiBitBool4::False.0 as u64;

    /// A basic set of flash properties.
    pub fn basic() -> Self {
        FlashFlags {
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            high_endurance: true,
            ..Default::default()
        }
    }

    /// A set of flash properties appropriate for the ROM_EXT region.
    pub fn rom_ext() -> Self {
        Self {
            read: true,
            program: true,
            erase: true,
            protect_when_primary: true,
            ..Default::default()
        }
    }

    /// A set of flash properties appropriate for the owner firmware region.
    pub fn firmware() -> Self {
        Self {
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            protect_when_primary: true,
            ..Default::default()
        }
    }

    /// A set of flash properties appropriate for the owner filesystem region.
    pub fn filesystem() -> Self {
        Self {
            read: true,
            program: true,
            erase: true,
            high_endurance: true,
            ..Default::default()
        }
    }

    /// A set of flash properties appropriate for owner info pages.
    pub fn info_page() -> Self {
        Self {
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            ..Default::default()
        }
    }
}

impl From<u64> for FlashFlags {
    fn from(flags: u64) -> Self {
        #[rustfmt::skip]
        let value = Self {
            // First 32-bit word: access/protection flags.
            read:                 flags & 0xF == Self::TRUE,
            program:              (flags >> 4) & 0xF == Self::TRUE,
            erase:                (flags >> 8) & 0xF == Self::TRUE,
            protect_when_primary: (flags >> 24) & 0xF == Self::TRUE,
            lock:                 (flags >> 28) & 0xF == Self::TRUE,

            // Second 32-bit word: flash properties.
            scramble:             (flags >> 32) & 0xF == Self::TRUE,
            ecc:                  (flags >> 36) & 0xF == Self::TRUE,
            high_endurance:       (flags >> 40) & 0xF == Self::TRUE,
        };
        value
    }
}

impl From<FlashFlags> for u64 {
    fn from(flags: FlashFlags) -> u64 {
        #[rustfmt::skip]
        let value =
            // First 32-bit word: access/protection flags.
            if flags.read                 { FlashFlags::TRUE } else { FlashFlags::FALSE } |
            if flags.program              { FlashFlags::TRUE } else { FlashFlags::FALSE } << 4 |
            if flags.erase                { FlashFlags::TRUE } else { FlashFlags::FALSE } << 8 |
            if flags.protect_when_primary { FlashFlags::TRUE } else { FlashFlags::FALSE } << 24 |
            if flags.lock                 { FlashFlags::TRUE } else { FlashFlags::FALSE } << 28 |

            // Second 32-bit word: flash properties.
            if flags.scramble             { FlashFlags::TRUE } else { FlashFlags::FALSE } << 32 |
            if flags.ecc                  { FlashFlags::TRUE } else { FlashFlags::FALSE } << 36 |
            if flags.high_endurance       { FlashFlags::TRUE } else { FlashFlags::FALSE } << 40 ;
        value
    }
}

/// Describes a region to which a set of flags apply.
#[derive(Debug, Default, Serialize, Deserialize, Annotate)]
pub struct OwnerFlashRegion {
    /// The start of the region (in pages).
    pub start: u16,
    /// The size of the region (in pages).
    pub size: u16,
    #[serde(flatten)]
    pub flags: FlashFlags,
}

impl OwnerFlashRegion {
    const SIZE: usize = 12;
    pub fn new(start: u16, size: u16, flags: FlashFlags) -> Self {
        Self { start, size, flags }
    }
    pub fn read(src: &mut impl Read, crypt: u64) -> Result<Self> {
        let start = src.read_u16::<LittleEndian>()?;
        let size = src.read_u16::<LittleEndian>()?;
        let flags = FlashFlags::from(src.read_u64::<LittleEndian>()? ^ crypt);
        Ok(Self { start, size, flags })
    }
    pub fn write(&self, dest: &mut impl Write, crypt: u64) -> Result<()> {
        dest.write_u16::<LittleEndian>(self.start)?;
        dest.write_u16::<LittleEndian>(self.size)?;
        dest.write_u64::<LittleEndian>(u64::from(self.flags) ^ crypt)?;
        Ok(())
    }
}

/// Describes the overall flash configuration for data pages.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerFlashConfig {
    /// Header identifying this struct.
    #[serde(
        skip_serializing_if = "GlobalFlags::not_debug",
        default = "OwnerFlashConfig::default_header"
    )]
    pub header: TlvHeader,
    /// A list of flash region configurations.
    pub config: Vec<OwnerFlashRegion>,
}

impl Default for OwnerFlashConfig {
    fn default() -> Self {
        Self {
            header: Self::default_header(),
            config: Vec::new(),
        }
    }
}

impl OwnerFlashConfig {
    const BASE_SIZE: usize = 8;

    pub fn default_header() -> TlvHeader {
        TlvHeader::new(TlvTag::FlashConfig, 0, "0.0")
    }
    pub fn basic() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::FlashConfig, 0, "0.0"),
            config: vec![
                OwnerFlashRegion::new(0, 32, FlashFlags::rom_ext()),
                OwnerFlashRegion::new(32, 192, FlashFlags::firmware()),
                OwnerFlashRegion::new(224, 32, FlashFlags::filesystem()),
                OwnerFlashRegion::new(256, 32, FlashFlags::rom_ext()),
                OwnerFlashRegion::new(256 + 32, 192, FlashFlags::firmware()),
                OwnerFlashRegion::new(256 + 224, 32, FlashFlags::filesystem()),
            ],
        }
    }
    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let config_len = (header.length - Self::BASE_SIZE) / OwnerFlashRegion::SIZE;
        let mut config = Vec::new();
        for i in 0..config_len {
            let crypt = 0x1111_1111_1111_1111u64 * (i as u64);
            config.push(OwnerFlashRegion::read(src, crypt)?)
        }
        Ok(Self { header, config })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::FlashConfig,
            Self::BASE_SIZE + self.config.len() * OwnerFlashRegion::SIZE,
            "0.0",
        );
        header.write(dest)?;
        for (i, config) in self.config.iter().enumerate() {
            let crypt = 0x1111_1111_1111_1111u64 * (i as u64);
            config.write(dest, crypt)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    #[rustfmt::skip]
    const OWNER_FLASH_CONFIG_BIN: &str =
r#"00000000: 46 4c 53 48 2c 00 00 00 00 00 00 00 96 09 00 99  FLSH,...........
00000010: 69 09 00 00 01 00 02 00 77 18 11 88 88 18 11 11  i.......w.......
00000020: 03 00 05 00 44 24 22 bb 44 24 22 22              ....D$".D$""
"#;

    const OWNER_FLASH_CONFIG_JSON: &str = r#"{
  config: [
    {
      start: 0,
      size: 0,
      read: true,
      program: false,
      erase: false,
      scramble: false,
      ecc: true,
      high_endurance: false,
      protect_when_primary: false,
      lock: false
    },
    {
      start: 1,
      size: 2,
      read: true,
      program: true,
      erase: false,
      scramble: false,
      ecc: false,
      high_endurance: false,
      protect_when_primary: false,
      lock: false
    },
    {
      start: 3,
      size: 5,
      read: true,
      program: true,
      erase: true,
      scramble: true,
      ecc: true,
      high_endurance: true,
      protect_when_primary: false,
      lock: false
    }
  ]
}"#;

    #[test]
    fn test_owner_flash_config_write() -> Result<()> {
        let ofr = OwnerFlashConfig {
            header: TlvHeader::default(),
            config: vec![
                OwnerFlashRegion::new(
                    0,
                    0,
                    FlashFlags {
                        read: true,
                        ecc: true,
                        ..Default::default()
                    },
                ),
                OwnerFlashRegion::new(
                    1,
                    2,
                    FlashFlags {
                        read: true,
                        program: true,
                        ..Default::default()
                    },
                ),
                OwnerFlashRegion::new(3, 5, FlashFlags::basic()),
            ],
        };
        let mut bin = Vec::new();
        ofr.write(&mut bin)?;
        eprintln!("{}", hexdump_string(&bin)?);
        assert_eq!(hexdump_string(&bin)?, OWNER_FLASH_CONFIG_BIN);
        Ok(())
    }

    #[test]
    fn test_owner_flash_config_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_FLASH_CONFIG_BIN)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let ofr = OwnerFlashConfig::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&ofr)?.to_json5().to_string();
        assert_eq!(doc, OWNER_FLASH_CONFIG_JSON);
        Ok(())
    }
}
