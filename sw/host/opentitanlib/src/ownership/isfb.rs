// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::io::{Read, Write};

use super::application_key::ApplicationKeyDomain;
use super::misc::{TlvHeader, TlvTag};
use super::GlobalFlags;

/// The owner Integration Specific Firmware Binding (ISFB) configuration
/// describes the configuration parameters for the ISFB region.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerIsfbConfig {
    /// Header identifying this struct.
    #[serde(
        skip_serializing_if = "GlobalFlags::not_debug",
        default = "OwnerIsfbConfig::default_header"
    )]
    pub header: TlvHeader,
    /// The flash bank where the ISFB is located.
    pub bank: u8,
    /// The info flash page where the ISFB is located.
    pub page: u8,
    /// Padding for alignment.
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
    #[annotate(format=hex)]
    pub pad: u16,

    /// The erase policy for the ISFB region.
    #[annotate(format=hex)]
    pub erase_conditions: u32,
    /// The key domain associated with the erase condition policy.
    #[annotate(format=hex)]
    pub key_domain: ApplicationKeyDomain,
    /// Reserved for future use.
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
    #[annotate(format=hex)]
    pub reserved: [u32; 5],
    /// Number of `uint32_t` reserved for product expressions. It has to be a
    /// value less than or equal to 256.
    pub product_words: u32,
}

impl Default for OwnerIsfbConfig {
    fn default() -> Self {
        Self {
            header: Self::default_header(),
            bank: 0u8,
            page: 0u8,
            pad: 0u16,
            erase_conditions: 0u32,
            key_domain: ApplicationKeyDomain::default(),
            reserved: [0u32; 5],
            product_words: 0u32,
        }
    }
}

impl OwnerIsfbConfig {
    const SIZE: usize = 2048;
    pub fn default_header() -> TlvHeader {
        TlvHeader::new(TlvTag::IntegratorSpecificFirmwareBinding, Self::SIZE, "0.0")
    }
    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let bank = src.read_u8()?;
        let page = src.read_u8()?;
        let pad = src.read_u16::<LittleEndian>()?;
        let erase_conditions = src.read_u32::<LittleEndian>()?;
        let key_domain = ApplicationKeyDomain(src.read_u32::<LittleEndian>()?);
        let mut reserved = [0u32; 5];
        src.read_u32_into::<LittleEndian>(&mut reserved)?;
        let product_words = src.read_u32::<LittleEndian>()?;
        Ok(Self {
            header,
            bank,
            page,
            pad,
            erase_conditions,
            key_domain,
            reserved,
            product_words,
        })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = Self::default_header();
        header.write(dest)?;

        dest.write_u8(self.bank)?;
        dest.write_u8(self.page)?;
        dest.write_u16::<LittleEndian>(self.pad)?;
        dest.write_u32::<LittleEndian>(self.erase_conditions)?;
        dest.write_u32::<LittleEndian>(u32::from(self.key_domain))?;
        for x in &self.reserved {
            dest.write_u32::<LittleEndian>(*x)?;
        }
        dest.write_u32::<LittleEndian>(self.product_words)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    const OWNER_ISFB_CONF: &str = "\
00000000: 49 53 46 42 00 08 00 00 01 08 00 00 66 06 00 00  ISFB........f...
00000010: 70 72 6f 64 00 00 00 00 00 00 00 00 00 00 00 00  prod............
00000020: 00 00 00 00 00 00 00 00 80 00 00 00              ............
";
    const OWNER_ISFB_CONF_JSON: &str = r#"{
  bank: 1,
  page: 8,
  erase_conditions: 0x666,
  key_domain: "Prod",
  product_words: 128
}"#;

    #[test]
    fn test_owner_isfb_config_write() -> Result<()> {
        let isfb = OwnerIsfbConfig {
            header: TlvHeader::default(),
            bank: 1,
            page: 8,
            pad: 0,
            erase_conditions: 0x0000_0666,
            key_domain: ApplicationKeyDomain::Prod,
            product_words: 128,
            ..Default::default()
        };

        let mut bin = Vec::new();
        isfb.write(&mut bin)?;
        eprintln!("{}", hexdump_string(&bin)?);
        assert_eq!(hexdump_string(&bin)?, OWNER_ISFB_CONF);
        Ok(())
    }

    #[test]
    fn test_owner_isfb_config_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_ISFB_CONF)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let orc = OwnerIsfbConfig::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&orc)?.to_json5().to_string();
        eprintln!("{}", doc);
        assert_eq!(doc, OWNER_ISFB_CONF_JSON);
        Ok(())
    }
}
