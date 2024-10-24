// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::convert::TryFrom;
use std::io::{Read, Write};

use super::misc::{KeyMaterial, OwnershipKeyAlg, TlvHeader, TlvTag};
use super::GlobalFlags;
use super::{OwnerApplicationKey, OwnerFlashConfig, OwnerFlashInfoConfig, OwnerRescueConfig};
use crate::crypto::ecdsa::{EcdsaPrivateKey, EcdsaRawSignature};
use crate::with_unknown;

with_unknown! {
    pub enum SramExecMode: u32 [default = Self::DisabledLocked] {
        DisabledLocked = u32::from_le_bytes(*b"LNEX"),
        Disabled = u32::from_le_bytes(*b"NOEX"),
        Enabled = u32::from_le_bytes(*b"EXEC"),
    }

    pub enum MinSecurityVersion: u32 [default = Self::NoChange] {
        NoChange = 0xFFFFFFFFu32,
    }

    pub enum OwnershipUpdateMode: u32 [default = Self::Open] {
        Open = u32::from_le_bytes(*b"OPEN"),
        UnlockSelf = u32::from_le_bytes(*b"SELF"),
        SelfVersion = u32::from_le_bytes(*b"SELV"),
        NewVersion = u32::from_le_bytes(*b"NEWV"),
    }
}

/// Describes the owner configuration and key material.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerBlock {
    /// Header identifying this struct.
    #[serde(
        skip_serializing_if = "GlobalFlags::not_debug",
        default = "OwnerBlock::default_header"
    )]
    pub header: TlvHeader,
    /// Configuraion version (monotonically increasing per owner).
    #[serde(default)]
    pub config_version: u32,
    /// Whether the owner wants to permit code execution in SRAM.
    #[serde(default)]
    pub sram_exec: SramExecMode,
    /// The key algorithm of the ownership keys.
    pub ownership_key_alg: OwnershipKeyAlg,
    /// Ownership update mode.
    #[serde(default)]
    pub update_mode: OwnershipUpdateMode,
    /// Set the minimum security version to this value.
    #[serde(default)]
    pub min_security_version_bl0: MinSecurityVersion,
    /// The device ID locking constraint.
    #[serde(default)]
    pub lock_constraint: u32,
    /// The device ID to which this config applies.
    #[serde(
        default = "OwnerBlock::default_constraint",
        skip_serializing_if = "OwnerBlock::is_default_constraint"
    )]
    #[annotate(format=hex)]
    pub device_id: [u32; 8],
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
    #[annotate(format=hex)]
    pub reserved: [u32; 16],
    /// The owner identity key.
    pub owner_key: KeyMaterial,
    /// The owner activation key.
    pub activate_key: KeyMaterial,
    /// The owner unlock key.
    pub unlock_key: KeyMaterial,
    /// A list of other configuration items (application keys, flash configuration, etc).
    #[serde(default)]
    pub data: Vec<OwnerConfigItem>,
    #[serde(default, skip_serializing_if = "EcdsaRawSignature::is_empty")]
    #[annotate(format=hex)]
    /// A signature over this block with the owner key.
    pub signature: EcdsaRawSignature,
    /// A sealing value that locks a configuration to a particular device.
    #[serde(default, skip_serializing_if = "Vec::is_empty", with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub seal: Vec<u8>,
}

impl Default for OwnerBlock {
    fn default() -> Self {
        Self {
            header: Self::default_header(),
            config_version: 0,
            sram_exec: SramExecMode::default(),
            ownership_key_alg: OwnershipKeyAlg::default(),
            update_mode: OwnershipUpdateMode::default(),
            min_security_version_bl0: MinSecurityVersion::default(),
            lock_constraint: 0,
            device_id: Self::default_constraint(),
            reserved: [0u32; 16],
            owner_key: KeyMaterial::default(),
            activate_key: KeyMaterial::default(),
            unlock_key: KeyMaterial::default(),
            data: Vec::new(),
            signature: EcdsaRawSignature::default(),
            seal: Vec::new(),
        }
    }
}

impl OwnerBlock {
    pub const SIZE: usize = 2048;
    pub const DATA_SIZE: usize = 1536;
    pub const SIGNATURE_OFFSET: usize = 1952;
    // The not present value must be reflected in the TlvTag::NotPresent value.
    const NOT_PRESENT: u8 = 0x5a;
    const NO_CONSTRAINT: u32 = 0x7e7e7e7e;

    pub fn default_header() -> TlvHeader {
        TlvHeader::new(TlvTag::Owner, 0, "0.0")
    }
    pub fn basic() -> Self {
        Self {
            data: vec![
                OwnerConfigItem::ApplicationKey(OwnerApplicationKey::default()),
                OwnerConfigItem::FlashConfig(OwnerFlashConfig::basic()),
                OwnerConfigItem::FlashInfoConfig(OwnerFlashInfoConfig::basic()),
                OwnerConfigItem::RescueConfig(OwnerRescueConfig::all()),
            ],
            ..Default::default()
        }
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(TlvTag::Owner, Self::SIZE, "0.0");
        header.write(dest)?;
        dest.write_u32::<LittleEndian>(self.config_version)?;
        dest.write_u32::<LittleEndian>(u32::from(self.sram_exec))?;
        dest.write_u32::<LittleEndian>(u32::from(self.ownership_key_alg))?;
        dest.write_u32::<LittleEndian>(u32::from(self.update_mode))?;
        dest.write_u32::<LittleEndian>(u32::from(self.min_security_version_bl0))?;
        dest.write_u32::<LittleEndian>(self.lock_constraint)?;

        for (i, x) in self.device_id.iter().enumerate() {
            if self.lock_constraint & (1u32 << i) == 0 {
                dest.write_u32::<LittleEndian>(Self::NO_CONSTRAINT)?;
            } else {
                dest.write_u32::<LittleEndian>(*x)?;
            }
        }
        for x in &self.reserved {
            dest.write_u32::<LittleEndian>(*x)?;
        }
        self.owner_key.write_length(dest, 96)?;
        self.activate_key.write_length(dest, 96)?;
        self.unlock_key.write_length(dest, 96)?;
        let mut data = Vec::new();
        for item in &self.data {
            item.write(&mut data)?;
        }
        data.resize(Self::DATA_SIZE, Self::NOT_PRESENT);
        dest.write_all(&data)?;
        self.signature.write(dest)?;
        if self.seal.is_empty() {
            dest.write_all(&[0u8; 32])?;
        } else {
            dest.write_all(&self.seal)?;
        }
        Ok(())
    }

    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let config_version = src.read_u32::<LittleEndian>()?;
        let sram_exec = SramExecMode(src.read_u32::<LittleEndian>()?);
        let ownership_key_alg = OwnershipKeyAlg(src.read_u32::<LittleEndian>()?);
        let update_mode = OwnershipUpdateMode(src.read_u32::<LittleEndian>()?);
        let min_security_version_bl0 = MinSecurityVersion(src.read_u32::<LittleEndian>()?);
        let lock_constraint = src.read_u32::<LittleEndian>()?;

        let mut device_id = [0u32; 8];
        src.read_u32_into::<LittleEndian>(&mut device_id)?;
        let mut reserved = [0u32; 16];
        src.read_u32_into::<LittleEndian>(&mut reserved)?;
        let owner_key = KeyMaterial::read_length(src, ownership_key_alg, 96)?;
        let activate_key = KeyMaterial::read_length(src, ownership_key_alg, 96)?;
        let unlock_key = KeyMaterial::read_length(src, ownership_key_alg, 96)?;
        let mut bytes = vec![0u8; Self::DATA_SIZE];
        src.read_exact(&mut bytes)?;
        let mut cursor = std::io::Cursor::new(&bytes);
        let mut data = Vec::new();
        while cursor.position() as usize != Self::DATA_SIZE {
            match OwnerConfigItem::read(&mut cursor)? {
                Some(item) => data.push(item),
                None => break,
            }
        }
        let signature = EcdsaRawSignature::read(src)?;
        let mut seal = vec![0u8; 32];
        src.read_exact(&mut seal)?;
        Ok(Self {
            header,
            config_version,
            sram_exec,
            ownership_key_alg,
            update_mode,
            min_security_version_bl0,
            lock_constraint,
            device_id,
            reserved,
            owner_key,
            activate_key,
            unlock_key,
            data,
            signature,
            seal,
        })
    }
    pub fn sign(&mut self, key: &EcdsaPrivateKey) -> Result<()> {
        let mut data = Vec::new();
        self.write(&mut data)?;
        self.signature = key.digest_and_sign(&data[..Self::SIGNATURE_OFFSET])?;
        Ok(())
    }

    pub fn is_default_constraint(d: &[u32; 8]) -> bool {
        *d == [Self::NO_CONSTRAINT; 8]
    }

    pub fn default_constraint() -> [u32; 8] {
        [Self::NO_CONSTRAINT; 8]
    }
}

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub enum OwnerConfigItem {
    #[serde(alias = "application_key")]
    ApplicationKey(OwnerApplicationKey),
    #[serde(alias = "flash_info_config")]
    FlashInfoConfig(OwnerFlashInfoConfig),
    #[serde(alias = "flash_config")]
    FlashConfig(OwnerFlashConfig),
    #[serde(alias = "rescue_config")]
    RescueConfig(OwnerRescueConfig),
    #[serde(alias = "raw")]
    Raw(
        #[serde(with = "serde_bytes")]
        #[annotate(format = hexdump)]
        Vec<u8>,
    ),
}

impl OwnerConfigItem {
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        match self {
            Self::ApplicationKey(x) => x.write(dest)?,
            Self::FlashInfoConfig(x) => x.write(dest)?,
            Self::FlashConfig(x) => x.write(dest)?,
            Self::RescueConfig(x) => x.write(dest)?,
            Self::Raw(x) => dest.write_all(x)?,
        }
        Ok(())
    }

    pub fn read(src: &mut impl Read) -> Result<Option<Self>> {
        let header = TlvHeader::read(src)?;
        let item = match header.identifier {
            TlvTag::ApplicationKey => Self::ApplicationKey(OwnerApplicationKey::read(src, header)?),
            TlvTag::FlashConfig => Self::FlashConfig(OwnerFlashConfig::read(src, header)?),
            TlvTag::FlashInfoConfig => {
                Self::FlashInfoConfig(OwnerFlashInfoConfig::read(src, header)?)
            }
            TlvTag::Rescue => Self::RescueConfig(OwnerRescueConfig::read(src, header)?),
            TlvTag::NotPresent => return Ok(None),
            _ => {
                let mut data = Vec::new();
                header.write(&mut data)?;
                if header.length >= TlvHeader::SIZE && header.length < OwnerBlock::DATA_SIZE {
                    data.resize(header.length, 0);
                    let len = src.read(&mut data)?;
                    data.resize(len, 0);
                } else {
                    src.read_to_end(&mut data)?;
                }
                Self::Raw(data)
            }
        };
        Ok(Some(item))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::crypto::ecdsa::EcdsaRawPublicKey;
    use crate::ownership::{
        ApplicationKeyDomain, FlashFlags, OwnerFlashInfoConfig, OwnerFlashRegion, OwnerInfoPage,
        OwnerRescueConfig,
    };
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    #[rustfmt::skip]
    const OWNER_BIN: &str =
r#"00000000: 4f 57 4e 52 00 08 00 00 00 00 00 00 4c 4e 45 58  OWNR........LNEX
00000010: 50 32 35 36 4f 50 45 4e ff ff ff ff 00 00 00 00  P256OPEN........
00000020: 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e  ~~~~~~~~~~~~~~~~
00000030: 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e 7e  ~~~~~~~~~~~~~~~~
00000040: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000050: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000060: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000070: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000080: 11 11 11 11 11 11 11 11 11 11 11 11 11 11 11 11  ................
00000090: 11 11 11 11 11 11 11 11 11 11 11 11 11 11 11 11  ................
000000a0: 21 21 21 21 21 21 21 21 21 21 21 21 21 21 21 21  !!!!!!!!!!!!!!!!
000000b0: 21 21 21 21 21 21 21 21 21 21 21 21 21 21 21 21  !!!!!!!!!!!!!!!!
000000c0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000d0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000000e0: 33 33 33 33 33 33 33 33 33 33 33 33 33 33 33 33  3333333333333333
000000f0: 33 33 33 33 33 33 33 33 33 33 33 33 33 33 33 33  3333333333333333
00000100: 44 44 44 44 44 44 44 44 44 44 44 44 44 44 44 44  DDDDDDDDDDDDDDDD
00000110: 44 44 44 44 44 44 44 44 44 44 44 44 44 44 44 44  DDDDDDDDDDDDDDDD
00000120: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000130: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000140: 55 55 55 55 55 55 55 55 55 55 55 55 55 55 55 55  UUUUUUUUUUUUUUUU
00000150: 55 55 55 55 55 55 55 55 55 55 55 55 55 55 55 55  UUUUUUUUUUUUUUUU
00000160: 66 66 66 66 66 66 66 66 66 66 66 66 66 66 66 66  ffffffffffffffff
00000170: 66 66 66 66 66 66 66 66 66 66 66 66 66 66 66 66  ffffffffffffffff
00000180: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
00000190: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000001a0: 41 50 50 4b 70 00 00 00 50 32 35 36 70 72 6f 64  APPKp...P256prod
000001b0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000001c0: 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00  ................
000001d0: aa aa aa aa aa aa aa aa aa aa aa aa aa aa aa aa  ................
000001e0: aa aa aa aa aa aa aa aa aa aa aa aa aa aa aa aa  ................
000001f0: bb bb bb bb bb bb bb bb bb bb bb bb bb bb bb bb  ................
00000200: bb bb bb bb bb bb bb bb bb bb bb bb bb bb bb bb  ................
00000210: 46 4c 53 48 20 00 00 00 00 00 00 01 66 06 00 99  FLSH .......f...
00000220: 66 06 00 00 00 01 00 02 77 17 11 88 77 17 11 11  f.......w...w...
00000230: 49 4e 46 4f 20 00 00 00 00 01 00 00 66 06 00 99  INFO .......f...
00000240: 66 06 00 00 01 05 00 00 77 17 11 88 77 17 11 11  f.......w...w...
00000250: 52 45 53 51 50 00 00 00 58 4d 44 4d 20 00 e0 00  RESQP...XMDM ...
00000260: 45 4d 50 54 4d 53 45 43 4e 45 58 54 55 4e 4c 4b  EMPTMSECNEXTUNLK
00000270: 41 43 54 56 51 53 45 52 42 53 45 52 4f 42 45 52  ACTVQSERBSEROBER
00000280: 47 4f 4c 42 51 45 52 42 50 53 52 42 52 4e 57 4f  GOLBQERBPSRBRNWO
00000290: 30 47 50 4f 31 47 50 4f 44 49 54 4f 54 49 41 57  0GPO1GPODITOTIAW
000002a0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000002b0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000002c0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000002d0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000002e0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000002f0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000300: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000310: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000320: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000330: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000340: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000350: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000360: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000370: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000380: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000390: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003a0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003b0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003c0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003d0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003e0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000003f0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000400: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000410: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000420: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000430: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000440: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000450: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000460: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000470: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000480: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000490: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004a0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004b0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004c0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004d0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004e0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000004f0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000500: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000510: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000520: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000530: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000540: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000550: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000560: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000570: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000580: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000590: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005a0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005b0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005c0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005d0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005e0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000005f0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000600: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000610: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000620: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000630: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000640: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000650: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000660: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000670: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000680: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000690: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006a0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006b0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006c0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006d0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006e0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000006f0: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000700: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000710: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000720: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000730: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000740: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000750: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000760: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000770: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000780: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
00000790: 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a 5a  ZZZZZZZZZZZZZZZZ
000007a0: 77 77 77 77 77 77 77 77 77 77 77 77 77 77 77 77  wwwwwwwwwwwwwwww
000007b0: 77 77 77 77 77 77 77 77 77 77 77 77 77 77 77 77  wwwwwwwwwwwwwwww
000007c0: 88 88 88 88 88 88 88 88 88 88 88 88 88 88 88 88  ................
000007d0: 88 88 88 88 88 88 88 88 88 88 88 88 88 88 88 88  ................
000007e0: ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff  ................
000007f0: ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff ff  ................
"#;

    const OWNER_JSON: &str = r#"{
  config_version: 0,
  sram_exec: "DisabledLocked",
  ownership_key_alg: "EcdsaP256",
  update_mode: "Open",
  min_security_version_bl0: "NoChange",
  lock_constraint: 0,
  owner_key: {
    Ecdsa: {
      x: "1111111111111111111111111111111111111111111111111111111111111111",
      y: "2121212121212121212121212121212121212121212121212121212121212121"
    }
  },
  activate_key: {
    Ecdsa: {
      x: "3333333333333333333333333333333333333333333333333333333333333333",
      y: "4444444444444444444444444444444444444444444444444444444444444444"
    }
  },
  unlock_key: {
    Ecdsa: {
      x: "5555555555555555555555555555555555555555555555555555555555555555",
      y: "6666666666666666666666666666666666666666666666666666666666666666"
    }
  },
  data: [
    {
      ApplicationKey: {
        key_alg: "EcdsaP256",
        key_domain: "Prod",
        key_diversifier: [
          0x0,
          0x0,
          0x0,
          0x0,
          0x0,
          0x0,
          0x0
        ],
        usage_constraint: 0x0,
        key: {
          Ecdsa: {
            x: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            y: "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
          }
        }
      }
    },
    {
      FlashConfig: {
        config: [
          {
            start: 0,
            size: 256,
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            high_endurance: true,
            protect_when_active: false,
            lock: false
          },
          {
            start: 256,
            size: 512,
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            high_endurance: true,
            protect_when_active: false,
            lock: false
          }
        ]
      }
    },
    {
      FlashInfoConfig: {
        config: [
          {
            bank: 0,
            page: 1,
            pad: 0,
            read: true,
            program: true,
            erase: true,
            scramble: true,
            ecc: true,
            high_endurance: true,
            protect_when_active: false,
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
            protect_when_active: false,
            lock: false
          }
        ]
      }
    },
    {
      RescueConfig: {
        rescue_type: "Xmodem",
        start: 32,
        size: 224,
        command_allow: [
          "Empty",
          "MinBl0SecVerRequest",
          "NextBl0SlotRequest",
          "OwnershipUnlockRequest",
          "OwnershipActivateRequest",
          "Rescue",
          "RescueB",
          "Reboot",
          "GetBootLog",
          "BootSvcReq",
          "BootSvcRsp",
          "OwnerBlock",
          "GetOwnerPage0",
          "GetOwnerPage1",
          "GetDeviceId",
          "Wait"
        ]
      }
    }
  ],
  signature: {
    r: "7777777777777777777777777777777777777777777777777777777777777777",
    s: "8888888888888888888888888888888888888888888888888888888888888888"
  },
  seal: "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
}"#;

    #[test]
    fn test_owner_write() -> Result<()> {
        let own = OwnerBlock {
            config_version: 0,
            sram_exec: SramExecMode::default(),
            ownership_key_alg: OwnershipKeyAlg::EcdsaP256,
            owner_key: KeyMaterial::Ecdsa(EcdsaRawPublicKey {
                x: hex::decode("1111111111111111111111111111111111111111111111111111111111111111")?,
                y: hex::decode("2121212121212121212121212121212121212121212121212121212121212121")?,
            }),
            activate_key: KeyMaterial::Ecdsa(EcdsaRawPublicKey {
                x: hex::decode("3333333333333333333333333333333333333333333333333333333333333333")?,
                y: hex::decode("4444444444444444444444444444444444444444444444444444444444444444")?,
            }),
            unlock_key: KeyMaterial::Ecdsa(EcdsaRawPublicKey {
                x: hex::decode("5555555555555555555555555555555555555555555555555555555555555555")?,
                y: hex::decode("6666666666666666666666666666666666666666666666666666666666666666")?,
            }),
            data: vec![
                OwnerConfigItem::ApplicationKey(OwnerApplicationKey {
                    key_alg: OwnershipKeyAlg::EcdsaP256,
                    key_domain: ApplicationKeyDomain::Prod,
                    key: KeyMaterial::Ecdsa(EcdsaRawPublicKey {
                        x: hex::decode(
                            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                        )?,
                        y: hex::decode(
                            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                        )?,
                    }),
                    ..Default::default()
                }),
                OwnerConfigItem::FlashConfig(OwnerFlashConfig {
                    config: vec![
                        OwnerFlashRegion {
                            start: 0x000,
                            size: 0x100,
                            flags: FlashFlags::basic(),
                        },
                        OwnerFlashRegion {
                            start: 0x100,
                            size: 0x200,
                            flags: FlashFlags::basic(),
                        },
                    ],
                    ..Default::default()
                }),
                OwnerConfigItem::FlashInfoConfig(OwnerFlashInfoConfig {
                    config: vec![
                        OwnerInfoPage::new(0, 1, FlashFlags::basic()),
                        OwnerInfoPage::new(1, 5, FlashFlags::basic()),
                    ],
                    ..Default::default()
                }),
                OwnerConfigItem::RescueConfig(OwnerRescueConfig::all()),
            ],
            signature: EcdsaRawSignature {
                r: hex::decode("7777777777777777777777777777777777777777777777777777777777777777")?,
                s: hex::decode("8888888888888888888888888888888888888888888888888888888888888888")?,
            },
            seal: hex::decode("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")?,
            ..Default::default()
        };
        let mut bin = Vec::new();
        own.write(&mut bin)?;
        eprintln!("{}", hexdump_string(&bin)?);
        assert_eq!(hexdump_string(&bin)?, OWNER_BIN);
        Ok(())
    }

    #[test]
    fn test_owner_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_BIN)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let own = OwnerBlock::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&own)?.to_json5().to_string();
        eprintln!("{}", doc);
        assert_eq!(doc, OWNER_JSON);
        Ok(())
    }
}
