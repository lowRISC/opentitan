// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::convert::TryFrom;
use std::io::{Read, Write};

use super::misc::{TlvHeader, TlvTag};
use crate::chip::boot_svc::BootSvcKind;
use crate::with_unknown;

with_unknown! {
    pub enum RescueType: u32 [default = Self::None] {
        None = 0,
        Xmodem = u32::from_le_bytes(*b"XMDM"),
    }

    pub enum CommandTag: u32 [default = Self::Unknown] {
        Unknown = 0,
        Empty = BootSvcKind::EmptyRequest.0,
        MinBl0SecVerRequest = BootSvcKind::MinBl0SecVerRequest.0,
        NextBl0SlotRequest = BootSvcKind::NextBl0SlotRequest.0,
        UnlockOwnershipRequest = BootSvcKind::OwnershipUnlockRequest.0,
        ActivateOwnerRequest = BootSvcKind::OwnershipActivateRequest.0,
        Rescue = u32::from_le_bytes(*b"RESQ"),
        GetBootLog = u32::from_le_bytes(*b"BLOG"),
        BootSvcReq = u32::from_le_bytes(*b"BREQ"),
        BootSvcRsp = u32::from_le_bytes(*b"BRSP"),
        OwnerBlock = u32::from_le_bytes(*b"OWNR"),
    }
}

/// Describes the configuration of the rescue feature of the ROM_EXT.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerRescueConfig {
    /// Header identifying this struct.
    #[serde(default)]
    pub header: TlvHeader,
    /// The type of rescue protocol to use (ie: Xmodem).
    pub rescue_type: RescueType,
    /// The start of the rescue flash region (in pages).
    pub start: u16,
    /// The size of the rescue flash region (in pages).
    pub size: u16,
    /// An allow-list of commands permitted to be executed by the rescue module.
    pub command_allow: Vec<CommandTag>,
}

impl Default for OwnerRescueConfig {
    fn default() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::Rescue, 0),
            rescue_type: RescueType::default(),
            start: 0u16,
            size: 0u16,
            command_allow: Vec::new(),
        }
    }
}

impl OwnerRescueConfig {
    const BASE_SIZE: usize = 16;
    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let rescue_type = RescueType(src.read_u32::<LittleEndian>()?);
        let start = src.read_u16::<LittleEndian>()?;
        let size = src.read_u16::<LittleEndian>()?;
        let allow_len = (header.length - Self::BASE_SIZE) / std::mem::size_of::<u32>();
        let mut command_allow = Vec::new();
        for _ in 0..allow_len {
            command_allow.push(CommandTag(src.read_u32::<LittleEndian>()?));
        }
        Ok(Self {
            header,
            rescue_type,
            start,
            size,
            command_allow,
        })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::Rescue,
            Self::BASE_SIZE + self.command_allow.len() * std::mem::size_of::<u32>(),
        );
        header.write(dest)?;
        dest.write_u32::<LittleEndian>(u32::from(self.rescue_type))?;
        dest.write_u16::<LittleEndian>(self.start)?;
        dest.write_u16::<LittleEndian>(self.size)?;
        for allow in self.command_allow.iter() {
            dest.write_u32::<LittleEndian>(u32::from(*allow))?;
        }
        Ok(())
    }

    pub fn all() -> Self {
        OwnerRescueConfig {
            rescue_type: RescueType::Xmodem,
            // Start after the ROM_EXT.
            start: 32,
            // End at the end of the partition.
            size: 224,
            command_allow: vec![
                CommandTag::Empty,
                CommandTag::MinBl0SecVerRequest,
                CommandTag::NextBl0SlotRequest,
                CommandTag::UnlockOwnershipRequest,
                CommandTag::ActivateOwnerRequest,
                CommandTag::Rescue,
                CommandTag::GetBootLog,
                CommandTag::BootSvcReq,
                CommandTag::BootSvcRsp,
                CommandTag::OwnerBlock,
            ],
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    const OWNER_RESCUE_CONFIG_BIN: &str = "\
00000000: 52 45 53 51 38 00 00 00 58 4d 44 4d 20 00 64 00  RESQ8...XMDM .d.\n\
00000010: 45 4d 50 54 4d 53 45 43 4e 45 58 54 55 4e 4c 4b  EMPTMSECNEXTUNLK\n\
00000020: 41 43 54 56 52 45 53 51 42 4c 4f 47 42 52 45 51  ACTVRESQBLOGBREQ\n\
00000030: 42 52 53 50 4f 57 4e 52                          BRSPOWNR\n\
";
    const OWNER_RESCUE_CONFIG_JSON: &str = r#"{
  header: {
    identifier: "Rescue",
    length: 56
  },
  rescue_type: "Xmodem",
  start: 32,
  size: 100,
  command_allow: [
    "Empty",
    "MinBl0SecVerRequest",
    "NextBl0SlotRequest",
    "UnlockOwnershipRequest",
    "ActivateOwnerRequest",
    "Rescue",
    "GetBootLog",
    "BootSvcReq",
    "BootSvcRsp",
    "OwnerBlock"
  ]
}"#;

    #[test]
    fn test_owner_rescue_config_write() -> Result<()> {
        let orc = OwnerRescueConfig {
            header: TlvHeader::default(),
            rescue_type: RescueType::Xmodem,
            start: 32,
            size: 100,
            command_allow: vec![
                CommandTag::Empty,
                CommandTag::MinBl0SecVerRequest,
                CommandTag::NextBl0SlotRequest,
                CommandTag::UnlockOwnershipRequest,
                CommandTag::ActivateOwnerRequest,
                CommandTag::Rescue,
                CommandTag::GetBootLog,
                CommandTag::BootSvcReq,
                CommandTag::BootSvcRsp,
                CommandTag::OwnerBlock,
            ],
        };

        let mut bin = Vec::new();
        orc.write(&mut bin)?;
        eprintln!("{}", hexdump_string(&bin)?);
        assert_eq!(hexdump_string(&bin)?, OWNER_RESCUE_CONFIG_BIN);
        Ok(())
    }

    #[test]
    fn test_owner_rescue_config_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_RESCUE_CONFIG_BIN)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let orc = OwnerRescueConfig::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&orc)?.to_json5().to_string();
        eprintln!("{}", doc);
        assert_eq!(doc, OWNER_RESCUE_CONFIG_JSON);
        Ok(())
    }
}
