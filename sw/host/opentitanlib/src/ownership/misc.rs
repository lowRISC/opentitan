// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::cmp::Ordering;
use std::io::{Read, Write};

use crate::crypto::ecdsa::EcdsaRawPublicKey;
use crate::crypto::rsa::RsaRawPublicKey;
use crate::crypto::spx::SpxRawPublicKey;
use crate::crypto::Error;
use crate::util::serde::string_or_struct;
use crate::with_unknown;

with_unknown! {
    pub enum TlvTag: u32 [default = Self::Unknown] {
        Unknown = 0,
        Owner = u32::from_le_bytes(*b"OWNR"),
        ApplicationKey = u32::from_le_bytes(*b"APPK"),
        FlashConfig = u32::from_le_bytes(*b"FLSH"),
        FlashInfoConfig = u32::from_le_bytes(*b"INFO"),
        Rescue = u32::from_le_bytes(*b"RESQ"),
        DetachedSignature = u32::from_le_bytes(*b"SIGN"),
        IntegratorSpecificFirmwareBinding = u32::from_le_bytes(*b"ISFB"),
        NotPresent = u32::from_le_bytes(*b"ZZZZ"),
    }

    pub enum OwnershipKeyAlg: u32 [default = Self::Unknown] {
        Unknown = 0,
        Rsa = u32::from_le_bytes(*b"RSA3"),
        EcdsaP256 = u32::from_le_bytes(*b"P256"),
        SpxPure = u32::from_le_bytes(*b"S+Pu"),
        SpxPrehash = u32::from_le_bytes(*b"S+S2"),
        HybridSpxPure = u32::from_le_bytes(*b"H+Pu"),
        HybridSpxPrehash = u32::from_le_bytes(*b"H+S2"),
    }
}

impl OwnershipKeyAlg {
    pub fn is_detached(self) -> bool {
        !matches!(self, Self::EcdsaP256)
    }

    pub fn is_ecdsa(self) -> bool {
        matches!(
            self,
            Self::EcdsaP256 | Self::HybridSpxPure | Self::HybridSpxPrehash
        )
    }

    pub fn is_spx(self) -> bool {
        matches!(
            self,
            Self::SpxPure | Self::SpxPrehash | Self::HybridSpxPure | Self::HybridSpxPrehash
        )
    }

    pub fn is_hybrid(self) -> bool {
        matches!(self, Self::HybridSpxPure | Self::HybridSpxPrehash)
    }

    pub fn is_prehashed(self) -> bool {
        matches!(self, Self::SpxPrehash | Self::HybridSpxPrehash)
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, Annotate)]
#[serde(try_from = "String", into = "String")]
pub struct StructVersion {
    pub major: u8,
    pub minor: u8,
}

impl TryFrom<&str> for StructVersion {
    type Error = anyhow::Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        if let Some((major, minor)) = s.split_once('.') {
            Ok(StructVersion {
                major: major.parse()?,
                minor: minor.parse()?,
            })
        } else {
            Ok(StructVersion {
                major: s.parse()?,
                minor: 0,
            })
        }
    }
}

impl TryFrom<String> for StructVersion {
    type Error = anyhow::Error;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        StructVersion::try_from(s.as_str())
    }
}

impl From<StructVersion> for String {
    fn from(sv: StructVersion) -> String {
        format!("{}.{}", sv.major, sv.minor)
    }
}

impl StructVersion {
    pub fn read(src: &mut impl Read) -> Result<Self> {
        Ok(Self {
            major: src.read_u8()?,
            minor: src.read_u8()?,
        })
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u8(self.major)?;
        dest.write_u8(self.minor)?;
        Ok(())
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Annotate)]
pub struct TlvHeader {
    #[serde(default)]
    pub identifier: TlvTag,
    #[serde(default)]
    pub length: usize,
    #[serde(default)]
    pub version: StructVersion,
}

impl TlvHeader {
    pub const SIZE: usize = 8;
    pub fn new(id: TlvTag, len: usize, version: &str) -> Self {
        Self {
            identifier: id,
            length: len,
            version: version.try_into().expect("major.minor version string"),
        }
    }

    pub fn read(src: &mut impl Read) -> Result<Self> {
        Ok(Self {
            identifier: TlvTag(src.read_u32::<LittleEndian>()?),
            length: src.read_u16::<LittleEndian>()? as usize,
            version: StructVersion::read(src)?,
        })
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.identifier))?;
        dest.write_u16::<LittleEndian>(self.length as u16)?;
        self.version.write(dest)?;
        Ok(())
    }
    pub fn write_len(&self, dest: &mut impl Write, length: usize) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.identifier))?;
        dest.write_u16::<LittleEndian>(length as u16)?;
        self.version.write(dest)?;
        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HybridRawPublicKey {
    #[serde(deserialize_with = "string_or_struct")]
    pub ecdsa: EcdsaRawPublicKey,
    #[serde(deserialize_with = "string_or_struct")]
    pub spx: SpxRawPublicKey,
}

impl HybridRawPublicKey {
    const SIZE: usize = EcdsaRawPublicKey::SIZE + SpxRawPublicKey::SIZE;

    pub fn read(src: &mut impl Read) -> Result<Self> {
        Ok(Self {
            ecdsa: EcdsaRawPublicKey::read(src)?,
            spx: SpxRawPublicKey::read(src)?,
        })
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        self.ecdsa.write(dest)?;
        self.spx.write(dest)?;
        Ok(())
    }
}

/// Low-level key material (ie: bit representation).
#[derive(Debug, Serialize, Deserialize)]
#[allow(clippy::len_without_is_empty)]
pub enum KeyMaterial {
    #[serde(alias = "unknown")]
    Unknown(Vec<u8>),
    #[serde(alias = "ecdsa")]
    Ecdsa(#[serde(deserialize_with = "string_or_struct")] EcdsaRawPublicKey),
    #[serde(alias = "rsa")]
    Rsa(#[serde(deserialize_with = "string_or_struct")] RsaRawPublicKey),
    #[serde(alias = "spx")]
    Spx(#[serde(deserialize_with = "string_or_struct")] SpxRawPublicKey),
    #[serde(alias = "hybrid")]
    Hybrid(HybridRawPublicKey),
}

impl Default for KeyMaterial {
    fn default() -> Self {
        Self::Unknown(Vec::default())
    }
}

impl KeyMaterial {
    pub fn len(&self) -> usize {
        match self {
            KeyMaterial::Ecdsa(_) => EcdsaRawPublicKey::SIZE,
            KeyMaterial::Rsa(_) => RsaRawPublicKey::SIZE,
            KeyMaterial::Spx(_) => SpxRawPublicKey::SIZE,
            KeyMaterial::Hybrid(_) => HybridRawPublicKey::SIZE,
            KeyMaterial::Unknown(u) => u.len(),
        }
    }

    pub fn kind(&self) -> OwnershipKeyAlg {
        match self {
            KeyMaterial::Ecdsa(_) => OwnershipKeyAlg::EcdsaP256,
            KeyMaterial::Rsa(_) => OwnershipKeyAlg::Rsa,
            KeyMaterial::Spx(_) => OwnershipKeyAlg::SpxPure,
            KeyMaterial::Hybrid(_) => OwnershipKeyAlg::HybridSpxPure,
            KeyMaterial::Unknown(_) => OwnershipKeyAlg::Unknown,
        }
    }

    pub fn read_length(src: &mut impl Read, kind: OwnershipKeyAlg, buflen: usize) -> Result<Self> {
        let result = match kind {
            OwnershipKeyAlg::Rsa => KeyMaterial::Rsa(RsaRawPublicKey::read(src)?),
            OwnershipKeyAlg::EcdsaP256 => KeyMaterial::Ecdsa(EcdsaRawPublicKey::read(src)?),
            OwnershipKeyAlg::SpxPure | OwnershipKeyAlg::SpxPrehash => {
                KeyMaterial::Spx(SpxRawPublicKey::read(src)?)
            }
            OwnershipKeyAlg::HybridSpxPure | OwnershipKeyAlg::HybridSpxPrehash => {
                KeyMaterial::Hybrid(HybridRawPublicKey::read(src)?)
            }
            _ => {
                return Err(
                    Error::InvalidPublicKey(anyhow!("Unknown key algorithm {}", kind)).into(),
                );
            }
        };
        let len = result.len();
        if buflen != 0 {
            match len.cmp(&buflen) {
                Ordering::Less => {
                    let mut discard = vec![0; buflen - len];
                    src.read_exact(&mut discard)?;
                }
                Ordering::Greater => {
                    return Err(Error::InvalidPublicKey(anyhow!(
                        "Key type {} does not fit in {} bytes",
                        kind,
                        buflen
                    ))
                    .into());
                }
                Ordering::Equal => {}
            };
        }
        Ok(result)
    }

    pub fn write_length(&self, dest: &mut impl Write, buflen: usize) -> Result<()> {
        match self {
            KeyMaterial::Ecdsa(k) => k.write(dest)?,
            KeyMaterial::Rsa(k) => k.write(dest)?,
            KeyMaterial::Spx(k) => k.write(dest)?,
            KeyMaterial::Hybrid(k) => k.write(dest)?,
            _ => {
                return Err(Error::InvalidPublicKey(anyhow!("Unknown key type")).into());
            }
        };

        if buflen != 0 {
            let len = self.len();
            match len.cmp(&buflen) {
                Ordering::Less => {
                    let zero = vec![0; buflen - len];
                    dest.write_all(&zero)?;
                }
                Ordering::Greater => {
                    return Err(Error::InvalidPublicKey(anyhow!(
                        "Key type {} does not fit in {} bytes",
                        self.kind(),
                        buflen
                    ))
                    .into());
                }
                Ordering::Equal => {}
            };
        }
        Ok(())
    }
}
