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
use super::GlobalFlags;

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
    const SIZE: usize = 12;
    pub fn new(bank: u8, page: u8, flags: FlashFlags) -> Self {
        Self {
            bank,
            page,
            flags,
            ..Default::default()
        }
    }
    pub fn read(src: &mut impl Read, crypt: u64) -> Result<Self> {
        let bank = src.read_u8()?;
        let page = src.read_u8()?;
        let pad = src.read_u16::<LittleEndian>()?;
        let flags = FlashFlags::from(src.read_u64::<LittleEndian>()? ^ crypt);
        Ok(Self {
            bank,
            page,
            pad,
            flags,
        })
    }
    pub fn write(&self, dest: &mut impl Write, crypt: u64) -> Result<()> {
        dest.write_u8(self.bank)?;
        dest.write_u8(self.page)?;
        dest.write_u16::<LittleEndian>(self.pad)?;
        dest.write_u64::<LittleEndian>(u64::from(self.flags) ^ crypt)?;
        Ok(())
    }
}

/// Describes the overall flash configuration for owner-accesssable INFO pages.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerFlashInfoConfig {
    /// Header identifying this struct.
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
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
        for i in 0..config_len {
            let crypt = 0x1111_1111_1111_1111u64 * (i as u64);
            config.push(OwnerInfoPage::read(src, crypt)?)
        }
        Ok(Self { header, config })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::FlashInfoConfig,
            Self::BASE_SIZE + self.config.len() * OwnerInfoPage::SIZE,
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
    const OWNER_FLASH_INFO_CONFIG_BIN: &str =
r#"00000000: 49 4e 46 4f 2c 00 00 00 00 00 00 00 96 09 00 99  INFO,...........
00000010: 69 09 00 00 01 02 00 00 77 18 11 88 88 18 11 11  i.......w.......
00000020: 01 05 00 00 44 24 22 bb 44 24 22 22              ....D$".D$""
"#;

    const OWNER_FLASH_INFO_CONFIG_JSON: &str = r#"{
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
        eprintln!("{}", hexdump_string(&bin)?);
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
