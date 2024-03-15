// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};

use super::misc::{TlvHeader, TlvTag};

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

impl From<u32> for FlashFlags {
    fn from(flags: u32) -> Self {
        #[rustfmt::skip]
        let value = Self {
            read:                 flags & 0x00000001 != 0,
            program:              flags & 0x00000002 != 0,
            erase:                flags & 0x00000004 != 0,
            scramble:             flags & 0x00000008 != 0,
            ecc:                  flags & 0x00000010 != 0,
            high_endurance:       flags & 0x00000020 != 0,
            protect_when_primary: flags & 0x40000000 != 0,
            lock:                 flags & 0x80000000 != 0,
        };
        value
    }
}

impl From<FlashFlags> for u32 {
    fn from(flags: FlashFlags) -> u32 {
        #[rustfmt::skip]
        let value =
            if flags.read                 { 0x00000001 } else { 0 } |
            if flags.program              { 0x00000002 } else { 0 } |
            if flags.erase                { 0x00000004 } else { 0 } |
            if flags.scramble             { 0x00000008 } else { 0 } |
            if flags.ecc                  { 0x00000010 } else { 0 } |
            if flags.high_endurance       { 0x00000020 } else { 0 } |
            if flags.protect_when_primary { 0x40000000 } else { 0 } |
            if flags.lock                 { 0x80000000 } else { 0 } ;
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
    const SIZE: usize = 8;
    pub fn new(start: u16, size: u16, flags: FlashFlags) -> Self {
        Self { start, size, flags }
    }
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let start = src.read_u16::<LittleEndian>()?;
        let size = src.read_u16::<LittleEndian>()?;
        let flags = FlashFlags::from(src.read_u32::<LittleEndian>()?);
        Ok(Self { start, size, flags })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u16::<LittleEndian>(self.start)?;
        dest.write_u16::<LittleEndian>(self.size)?;
        dest.write_u32::<LittleEndian>(u32::from(self.flags))?;
        Ok(())
    }
}

/// Describes the overall flash configuration for data pages.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerFlashConfig {
    /// Header identifying this struct.
    #[serde(default)]
    pub header: TlvHeader,
    /// A list of flash region configurations.
    pub config: Vec<OwnerFlashRegion>,
}

impl Default for OwnerFlashConfig {
    fn default() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::FlashConfig, 0),
            config: Vec::new(),
        }
    }
}

impl OwnerFlashConfig {
    const BASE_SIZE: usize = 8;
    pub fn basic() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::FlashConfig, 0),
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
        for _ in 0..config_len {
            config.push(OwnerFlashRegion::read(src)?)
        }
        Ok(Self { header, config })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::FlashConfig,
            Self::BASE_SIZE + self.config.len() * OwnerFlashRegion::SIZE,
        );
        header.write(dest)?;
        for config in &self.config {
            config.write(dest)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    const OWNER_FLASH_CONFIG_BIN: &str = "\
00000000: 46 4c 53 48 20 00 00 00 00 00 00 00 11 00 00 00  FLSH ...........\n\
00000010: 01 00 02 00 03 00 00 00 03 00 05 00 3f 00 00 00  ............?...\n\
";
    const OWNER_FLASH_CONFIG_JSON: &str = r#"{
  header: {
    identifier: "FlashConfig",
    length: 32
  },
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
