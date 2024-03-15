// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};

use super::flash::FlashFlags;
use super::misc::{TlvHeader, TlvTag};

/// Describes an INFO page to which a set of flags apply.
#[derive(Debug, Default, Deserialize, Serialize, Annotate)]
pub struct OwnerInfoPage {
    /// The bank in which the info page resides.
    pub bank: u8,
    /// The info page number.
    pub page: u8,
    #[serde(default)]
    #[annotate(format=hex)]
    pub pad: u16,
    #[serde(flatten)]
    pub flags: FlashFlags,
}
impl OwnerInfoPage {
    const SIZE: usize = 8;
    pub fn new(bank: u8, page: u8, flags: FlashFlags) -> Self {
        Self {
            bank,
            page,
            flags,
            ..Default::default()
        }
    }
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let bank = src.read_u8()?;
        let page = src.read_u8()?;
        let pad = src.read_u16::<LittleEndian>()?;
        let flags = FlashFlags::from(src.read_u32::<LittleEndian>()?);
        Ok(Self {
            bank,
            page,
            pad,
            flags,
        })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u8(self.bank)?;
        dest.write_u8(self.page)?;
        dest.write_u16::<LittleEndian>(self.pad)?;
        dest.write_u32::<LittleEndian>(u32::from(self.flags))?;
        Ok(())
    }
}

/// Describes the overall flash configuration for owner-accesssable INFO pages.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerFlashInfoConfig {
    /// Header identifying this struct.
    #[serde(default)]
    pub header: TlvHeader,
    /// A list of info page configurations.
    pub config: Vec<OwnerInfoPage>,
}

impl Default for OwnerFlashInfoConfig {
    fn default() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::FlashInfoConfig, 0),
            config: Vec::new(),
        }
    }
}

impl OwnerFlashInfoConfig {
    const BASE_SIZE: usize = 8;

    pub fn basic() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::FlashInfoConfig, 0),
            config: vec![
                OwnerInfoPage::new(0, 6, FlashFlags::info_page()),
                OwnerInfoPage::new(0, 7, FlashFlags::info_page()),
                OwnerInfoPage::new(0, 8, FlashFlags::info_page()),
                OwnerInfoPage::new(0, 9, FlashFlags::info_page()),
            ],
        }
    }

    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let config_len = (header.length - Self::BASE_SIZE) / OwnerInfoPage::SIZE;
        let mut config = Vec::new();
        for _ in 0..config_len {
            config.push(OwnerInfoPage::read(src)?)
        }
        Ok(Self { header, config })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::FlashInfoConfig,
            Self::BASE_SIZE + self.config.len() * OwnerInfoPage::SIZE,
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

    const OWNER_FLASH_INFO_CONFIG_BIN: &str = "\
00000000: 49 4e 46 4f 20 00 00 00 00 00 00 00 11 00 00 00  INFO ...........\n\
00000010: 01 02 00 00 03 00 00 00 01 05 00 00 3f 00 00 00  ............?...\n\
";
    const OWNER_FLASH_INFO_CONFIG_JSON: &str = r#"{
  header: {
    identifier: "FlashInfoConfig",
    length: 32
  },
  config: [
    {
      bank: 0,
      page: 0,
      pad: 0,
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
      bank: 1,
      page: 2,
      pad: 0,
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
      bank: 1,
      page: 5,
      pad: 0,
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
    fn test_owner_flash_info_config_write() -> Result<()> {
        let ofic = OwnerFlashInfoConfig {
            header: TlvHeader::default(),
            config: vec![
                OwnerInfoPage::new(
                    0,
                    0,
                    FlashFlags {
                        read: true,
                        ecc: true,
                        ..Default::default()
                    },
                ),
                OwnerInfoPage::new(
                    1,
                    2,
                    FlashFlags {
                        read: true,
                        program: true,
                        ..Default::default()
                    },
                ),
                OwnerInfoPage::new(1, 5, FlashFlags::basic()),
            ],
        };
        let mut bin = Vec::new();
        ofic.write(&mut bin)?;
        assert_eq!(hexdump_string(&bin)?, OWNER_FLASH_INFO_CONFIG_BIN);
        Ok(())
    }

    #[test]
    fn test_owner_flash_info_confg_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_FLASH_INFO_CONFIG_BIN)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let orc = OwnerFlashInfoConfig::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&orc)?.to_json5().to_string();
        assert_eq!(doc, OWNER_FLASH_INFO_CONFIG_JSON);
        Ok(())
    }
}
