// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::Deserialize;
use serde_annotate::Annotate;
use std::convert::TryFrom;
use std::io::{Read, Write};

use super::GlobalFlags;
use super::misc::{TlvHeader, TlvTag};
use crate::chip::boot_svc::BootSvcKind;
use crate::with_unknown;

with_unknown! {
    pub enum RescueProtocol: u8 [default = Self::None] {
        None = 0,
        Xmodem = b'X',
        UsbDfu = b'U',
        SpiDfu = b'S',
    }

    pub enum RescueTrigger: u8 [default = Self::UartBreak] {
        None = 0,
        UartBreak = 1,
        Strapping = 2,
        Gpio = 3,
    }

    pub enum CommandTag: u32 [default = Self::Unknown] {
        Unknown = 0,
        Empty = BootSvcKind::EmptyRequest.0,
        MinBl0SecVerRequest = BootSvcKind::MinBl0SecVerRequest.0,
        NextBl0SlotRequest = BootSvcKind::NextBl0SlotRequest.0,
        OwnershipUnlockRequest = BootSvcKind::OwnershipUnlockRequest.0,
        OwnershipActivateRequest =   BootSvcKind::OwnershipActivateRequest.0,

        // The rescue protocol-level commands are represented in big-endian order.
        Rescue = u32::from_be_bytes(*b"RESQ"),
        RescueB = u32::from_be_bytes(*b"RESB"),
        Reboot = u32::from_be_bytes(*b"REBO"),
        GetBootLog = u32::from_be_bytes(*b"BLOG"),
        BootSvcReq = u32::from_be_bytes(*b"BREQ"),
        BootSvcRsp = u32::from_be_bytes(*b"BRSP"),
        OwnerBlock = u32::from_be_bytes(*b"OWNR"),
        GetOwnerPage0 = u32::from_be_bytes(*b"OPG0"),
        GetOwnerPage1 = u32::from_be_bytes(*b"OPG1"),
        GetDeviceId = u32::from_be_bytes(*b"OTID"),
        Wait = u32::from_be_bytes(*b"WAIT"),
    }
}

/// Describes the configuration of the rescue feature of the ROM_EXT.
#[derive(Debug, Deserialize, Annotate, PartialEq)]
pub struct OwnerRescueConfig {
    /// Header identifying this struct.
    #[serde(
        skip_serializing_if = "GlobalFlags::not_debug",
        default = "OwnerRescueConfig::default_header"
    )]
    pub header: TlvHeader,
    /// The type of rescue protocol to use (ie: Xmodem).
    #[serde(alias = "rescue_type")]
    pub protocol: RescueProtocol,
    /// The rescue triggering mechanism (UartBreak, Strapping or Gpio).
    #[serde(default)]
    pub trigger: RescueTrigger,
    /// The index of the trigger (e.g. Strapping combo or GPIO pin number).
    #[serde(default)]
    pub trigger_index: u8,
    /// Whether or not to enable the GPIO pull resistor (only if trigger is GPIO).
    #[serde(default)]
    pub gpio_pull_en: bool,
    /// The GPIO trigger value (only if trigger is GPIO).
    #[serde(default)]
    pub gpio_value: bool,
    /// Enter rescue mode if boot fails.
    pub enter_on_failure: bool,
    /// The inactivity timeout in seconds (zero means disabled).
    pub timeout: u8,
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
            header: Self::default_header(),
            protocol: RescueProtocol::default(),
            gpio_pull_en: false,
            gpio_value: false,
            enter_on_failure: false,
            timeout: 0,
            trigger: RescueTrigger::default(),
            trigger_index: 0,
            start: 0u16,
            size: 0u16,
            command_allow: Vec::new(),
        }
    }
}

impl OwnerRescueConfig {
    const BASE_SIZE: usize = 16;
    const GPIO_PULL_BIT: u8 = 0x02;
    const GPIO_VALUE_BIT: u8 = 0x01;
    const ENTER_ON_FAIL_BIT: u8 = 0x80;
    const TIMEOUT_MASK: u8 = 0x7f;
    const TRIGGER_SHIFT: u8 = 6;
    const INDEX_MASK: u8 = 0x3f;

    pub fn default_header() -> TlvHeader {
        TlvHeader::new(TlvTag::Rescue, 0, "0.0")
    }
    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let protocol = RescueProtocol(src.read_u8()?);
        let gpio = src.read_u8()?;
        let timeout = src.read_u8()?;
        let trigger = src.read_u8()?;
        let start = src.read_u16::<LittleEndian>()?;
        let size = src.read_u16::<LittleEndian>()?;
        let allow_len = (header.length - Self::BASE_SIZE) / std::mem::size_of::<u32>();
        let mut command_allow = Vec::new();
        for _ in 0..allow_len {
            command_allow.push(CommandTag(src.read_u32::<LittleEndian>()?));
        }
        Ok(Self {
            header,
            protocol,
            gpio_pull_en: gpio & Self::GPIO_PULL_BIT != 0,
            gpio_value: gpio & Self::GPIO_VALUE_BIT != 0,
            enter_on_failure: timeout & Self::ENTER_ON_FAIL_BIT != 0,
            timeout: timeout & Self::TIMEOUT_MASK,
            trigger: RescueTrigger(trigger >> Self::TRIGGER_SHIFT),
            trigger_index: trigger & Self::INDEX_MASK,
            start,
            size,
            command_allow,
        })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(
            TlvTag::Rescue,
            Self::BASE_SIZE + self.command_allow.len() * std::mem::size_of::<u32>(),
            "0.0",
        );
        header.write(dest)?;
        dest.write_u8(u8::from(self.protocol))?;
        dest.write_u8(
            if self.gpio_pull_en {
                Self::GPIO_PULL_BIT
            } else {
                0
            } | if self.gpio_value {
                Self::GPIO_VALUE_BIT
            } else {
                0
            },
        )?;
        dest.write_u8(
            self.timeout & Self::TIMEOUT_MASK
                | if self.enter_on_failure {
                    Self::ENTER_ON_FAIL_BIT
                } else {
                    0
                },
        )?;
        dest.write_u8(
            self.trigger_index & Self::INDEX_MASK | u8::from(self.trigger) << Self::TRIGGER_SHIFT,
        )?;
        dest.write_u16::<LittleEndian>(self.start)?;
        dest.write_u16::<LittleEndian>(self.size)?;
        for allow in self.command_allow.iter() {
            dest.write_u32::<LittleEndian>(u32::from(*allow))?;
        }
        Ok(())
    }

    pub fn all() -> Self {
        OwnerRescueConfig {
            protocol: RescueProtocol::Xmodem,
            trigger: RescueTrigger::UartBreak,
            // Start after the ROM_EXT.
            start: 32,
            // End at the end of the partition.
            size: 224,
            command_allow: vec![
                CommandTag::Empty,
                CommandTag::MinBl0SecVerRequest,
                CommandTag::NextBl0SlotRequest,
                CommandTag::OwnershipUnlockRequest,
                CommandTag::OwnershipActivateRequest,
                CommandTag::Rescue,
                CommandTag::RescueB,
                CommandTag::Reboot,
                CommandTag::GetBootLog,
                CommandTag::BootSvcReq,
                CommandTag::BootSvcRsp,
                CommandTag::OwnerBlock,
                CommandTag::GetOwnerPage0,
                CommandTag::GetOwnerPage1,
                CommandTag::GetDeviceId,
                CommandTag::Wait,
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
00000000: 52 45 53 51 4c 00 00 00 58 00 00 40 20 00 64 00  RESQL...X..@ .d.\n\
00000010: 45 4d 50 54 4d 53 45 43 4e 45 58 54 55 4e 4c 4b  EMPTMSECNEXTUNLK\n\
00000020: 41 43 54 56 51 53 45 52 42 53 45 52 47 4f 4c 42  ACTVQSERBSERGOLB\n\
00000030: 51 45 52 42 50 53 52 42 52 4e 57 4f 30 47 50 4f  QERBPSRBRNWO0GPO\n\
00000040: 31 47 50 4f 44 49 54 4f 54 49 41 57              1GPODITOTIAW\n\
";
    const OWNER_RESCUE_CONFIG_JSON: &str = r#"{
  protocol: "Xmodem",
  trigger: "UartBreak",
  trigger_index: 0,
  gpio_pull_en: false,
  gpio_value: false,
  enter_on_failure: false,
  timeout: 0,
  start: 32,
  size: 100,
  command_allow: [
    "Empty",
    "MinBl0SecVerRequest",
    "NextBl0SlotRequest",
    "OwnershipUnlockRequest",
    "OwnershipActivateRequest",
    "Rescue",
    "RescueB",
    "GetBootLog",
    "BootSvcReq",
    "BootSvcRsp",
    "OwnerBlock",
    "GetOwnerPage0",
    "GetOwnerPage1",
    "GetDeviceId",
    "Wait"
  ]
}"#;

    #[test]
    fn test_owner_rescue_config_write() -> Result<()> {
        let orc = OwnerRescueConfig {
            header: TlvHeader::default(),
            protocol: RescueProtocol::Xmodem,
            trigger: RescueTrigger::UartBreak,
            start: 32,
            size: 100,
            command_allow: vec![
                CommandTag::Empty,
                CommandTag::MinBl0SecVerRequest,
                CommandTag::NextBl0SlotRequest,
                CommandTag::OwnershipUnlockRequest,
                CommandTag::OwnershipActivateRequest,
                CommandTag::Rescue,
                CommandTag::RescueB,
                CommandTag::GetBootLog,
                CommandTag::BootSvcReq,
                CommandTag::BootSvcRsp,
                CommandTag::OwnerBlock,
                CommandTag::GetOwnerPage0,
                CommandTag::GetOwnerPage1,
                CommandTag::GetDeviceId,
                CommandTag::Wait,
            ],
            ..Default::default()
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
