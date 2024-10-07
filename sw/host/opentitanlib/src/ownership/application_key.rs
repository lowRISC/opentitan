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
use crate::with_unknown;

with_unknown! {
    pub enum ApplicationKeyDomain: u32 [default = Self::Unknown] {
        Unknown = 0,
        Test = u32::from_le_bytes(*b"test"),
        Dev = u32::from_le_bytes(*b"dev_"),
        Prod = u32::from_le_bytes(*b"prod"),
    }
}

/// The OwnerApplicationKey is used to verify the owner's firmware payload.
#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct OwnerApplicationKey {
    /// Header identifying this struct.
    #[serde(default, skip_serializing_if = "GlobalFlags::not_debug")]
    pub header: TlvHeader,
    /// The key algorithm for this key (ECDSA, SPX+, etc).
    pub key_alg: OwnershipKeyAlg,
    /// The application key domain (Test, Dev, Prod).
    pub key_domain: ApplicationKeyDomain,
    /// A key diversification constant.  The key domain and the diversifier value are concatenated
    /// and programmed into the key manager's binding registers.
    #[serde(default)]
    #[annotate(format=hex)]
    pub key_diversifier: [u32; 7],
    /// A usage constraint value.  This value must match the usage constraint in the manifest to
    /// allow this key to be used.
    #[serde(default)]
    #[annotate(format=hex)]
    pub usage_constraint: u32,
    /// The key material.
    pub key: KeyMaterial,
}

impl Default for OwnerApplicationKey {
    fn default() -> Self {
        Self {
            header: TlvHeader::new(TlvTag::ApplicationKey, 0),
            key_alg: OwnershipKeyAlg::default(),
            key_domain: ApplicationKeyDomain::default(),
            key_diversifier: [0u32; 7],
            usage_constraint: 0u32,
            key: KeyMaterial::default(),
        }
    }
}

impl OwnerApplicationKey {
    pub fn read(src: &mut impl Read, header: TlvHeader) -> Result<Self> {
        let key_alg = OwnershipKeyAlg(src.read_u32::<LittleEndian>()?);
        let key_domain = ApplicationKeyDomain(src.read_u32::<LittleEndian>()?);
        let mut key_diversifier = [0u32; 7];
        src.read_u32_into::<LittleEndian>(&mut key_diversifier)?;
        let usage_constraint = src.read_u32::<LittleEndian>()?;
        let key = KeyMaterial::read_length(src, key_alg, 0)?;
        Ok(Self {
            header,
            key_alg,
            key_domain,
            key_diversifier,
            usage_constraint,
            key,
        })
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        let header = TlvHeader::new(TlvTag::ApplicationKey, 48 + self.key.len());
        header.write(dest)?;
        dest.write_u32::<LittleEndian>(u32::from(self.key_alg))?;
        dest.write_u32::<LittleEndian>(u32::from(self.key_domain))?;
        for kd in &self.key_diversifier {
            dest.write_u32::<LittleEndian>(*kd)?;
        }
        dest.write_u32::<LittleEndian>(self.usage_constraint)?;
        self.key.write_length(dest, 0)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::crypto::ecdsa::EcdsaRawPublicKey;
    use crate::util::hexdump::{hexdump_parse, hexdump_string};

    const OWNER_APPLICATION_KEY_BIN: &str = "\
00000000: 41 50 50 4b 70 00 00 00 50 32 35 36 70 72 6f 64  APPKp...P256prod\n\
00000010: 00 00 00 00 99 00 00 00 66 00 00 00 aa 00 00 00  ........f.......\n\
00000020: 55 00 00 00 11 00 00 00 ee 00 00 00 77 00 00 00  U...........w...\n\
00000030: 00 00 00 00 10 00 00 00 20 00 00 00 30 00 00 00  ........ ...0...\n\
00000040: 40 00 00 00 50 00 00 00 60 00 00 00 70 00 00 00  @...P...`...p...\n\
00000050: 80 00 00 00 90 00 00 00 a0 00 00 00 b0 00 00 00  ................\n\
00000060: c0 00 00 00 d0 00 00 00 e0 00 00 00 f0 00 00 00  ................\n\
";
    const OWNER_APPLICATION_KEY_JSON: &str = r#"{
  key_alg: "EcdsaP256",
  key_domain: "Prod",
  key_diversifier: [
    0x0,
    0x99,
    0x66,
    0xAA,
    0x55,
    0x11,
    0xEE
  ],
  usage_constraint: 0x77,
  key: {
    Ecdsa: {
      x: "0000000010000000200000003000000040000000500000006000000070000000",
      y: "8000000090000000a0000000b0000000c0000000d0000000e0000000f0000000"
    }
  }
}"#;

    #[test]
    fn test_owner_application_key_write() -> Result<()> {
        let oak = OwnerApplicationKey {
            header: TlvHeader::default(),
            key_alg: OwnershipKeyAlg::EcdsaP256,
            key_domain: ApplicationKeyDomain::Prod,
            key_diversifier: [0x00, 0x99, 0x66, 0xAA, 0x55, 0x11, 0xEE],
            usage_constraint: 0x77,
            key: KeyMaterial::Ecdsa(EcdsaRawPublicKey {
                x: hex::decode("0000000010000000200000003000000040000000500000006000000070000000")?,
                y: hex::decode("8000000090000000a0000000b0000000c0000000d0000000e0000000f0000000")?,
            }),
        };
        let mut bin = Vec::new();
        oak.write(&mut bin)?;
        eprintln!("{}", hexdump_string(&bin)?);
        assert_eq!(hexdump_string(&bin)?, OWNER_APPLICATION_KEY_BIN);
        Ok(())
    }

    #[test]
    fn test_owner_application_key_read() -> Result<()> {
        let buf = hexdump_parse(OWNER_APPLICATION_KEY_BIN)?;
        let mut cur = std::io::Cursor::new(&buf);
        let header = TlvHeader::read(&mut cur)?;
        let oak = OwnerApplicationKey::read(&mut cur, header)?;
        let doc = serde_annotate::serialize(&oak)?.to_json5().to_string();
        eprintln!("{}", doc);
        assert_eq!(doc, OWNER_APPLICATION_KEY_JSON);
        Ok(())
    }
}
