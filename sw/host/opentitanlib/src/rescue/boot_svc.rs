// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::Serialize;
use serde_annotate::Annotate;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;
use std::io::{Read, Write};

use crate::chip::boolean::HardenedBool;
use crate::crypto::ecdsa::{EcdsaPrivateKey, EcdsaPublicKey, EcdsaRawPublicKey, EcdsaRawSignature};
use crate::rescue::RescueError;
use crate::with_unknown;

with_unknown! {
    pub enum NextBootBl0: u32 [default = Self::Unknown] {
        Unknown = 0,
        SlotA = 0x08c0d499,
        SlotB = 0x7821e03a,
    }

    pub enum BootDataSlot: u32 [default = Self::Unknown] {
        Unknown = 0,
        SlotA = 0x9cdc8d50,
        SlotB = 0xcd598a4a,
    }

    pub enum UnlockMode: u32 [default = Self::Unknown] {
        Unknown = 0,
        Any = 0x00594e41,
        Endorsed = 0x4f444e45,
        Update = 0x00445055,
        Abort = 0x54524241,
    }

    pub enum BootSvcKind: u32 [default = Self::Unknown] {
        Unknown = 0,
        Empty = 0xb4594546,
        MinBl0SecVerRequest = 0xdac59e6e,
        MinBl0SecVerResponse = 0x756385f1,
        NextBl0SlotRequest = 0xe1edf546,
        NextBl0SlotResponse = 0x657051be,
        PrimaryBl0SlotRequest = 0x3d6c47b8,
        PrimaryBl0SlotResponse = 0xf2a4a609,
        UnlockOwnershipRequest = 0x51524e55,
        UnlockOwnershipResponse = 0x53524e55,
        ActivateOwnerRequest = 0x51524f41,
        ActivateOwnerResponse = 0x53524f41,
    }
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct Header {
    #[annotate(format=hex)]
    digest: [u32; 8],
    #[annotate(format=hex)]
    identifier: u32,
    kind: BootSvcKind,
    length: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct Empty {
    #[annotate(format=hex)]
    payload: Vec<u32>,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct MinBl0SecVerRequest {
    ver: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct MinBl0SecVerResponse {
    ver: u32,
    status: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct NextBl0SlotRequest {
    next_bl0_slot: NextBootBl0,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct NextBl0SlotResponse {
    status: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct PrimaryBl0SlotRequest {
    primary_bl0_slot: BootDataSlot,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct PrimaryBl0SlotResponse {
    primary_bl0_slot: BootDataSlot,
    status: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct UnlockOwnershipRequest {
    unlock_mode: UnlockMode,
    #[serde(with = "serde_bytes")]
    #[annotate(format=hexdump)]
    reserved: Vec<u8>,
    #[annotate(format=hex)]
    nonce: u64,
    next_owner_key: EcdsaRawPublicKey,
    signature: EcdsaRawSignature,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct UnlockOwnershipResponse {
    status: u32,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct ActivateOwnerRequest {
    primary_bl0_slot: BootDataSlot,
    erase_previous: HardenedBool,
    #[serde(with = "serde_bytes")]
    #[annotate(format=hexdump)]
    reserved: Vec<u8>,
    nonce: u64,
    signature: EcdsaRawSignature,
}

#[derive(Debug, Default, Serialize, Annotate)]
pub struct ActivateOwnerResponse {
    status: u32,
}

#[derive(Debug, Serialize, Annotate)]
pub enum Message {
    Raw(
        #[serde(with = "serde_bytes")]
        #[annotate(format=hexdump)]
        Vec<u8>,
    ),
    Empty(Empty),
    MinBl0SecVerRequest(MinBl0SecVerRequest),
    NextBl0SlotRequest(NextBl0SlotRequest),
    PrimaryBl0SlotRequest(PrimaryBl0SlotRequest),
    UnlockOwnershipRequest(UnlockOwnershipRequest),
    ActivateOwnerRequest(ActivateOwnerRequest),
    MinBl0SecVerResponse(MinBl0SecVerResponse),
    NextBl0SlotResponse(NextBl0SlotResponse),
    PrimaryBl0SlotResponse(PrimaryBl0SlotResponse),
    UnlockOwnershipResponse(UnlockOwnershipResponse),
    ActivateOwnerResponse(ActivateOwnerResponse),
}

#[derive(Debug, Serialize, Annotate)]
pub struct BootSvc {
    header: Header,
    message: Message,
}

impl TryFrom<&[u8]> for BootSvc {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let header = Header::try_from(buf)?;
        let len = header.length as usize;
        if buf.len() - Header::SIZE < len {
            return Err(RescueError::BadSize(len, buf.len()));
        }
        let mut digest = Sha256::digest(&buf[Header::HASH_LEN..Header::SIZE]);
        digest.reverse();
        if digest[..] == buf[..Header::HASH_LEN] {
            return Err(RescueError::InvalidDigest);
        }
        let buf = &buf[Header::SIZE..];
        let message = match header.kind {
            BootSvcKind::Empty => Message::Empty(TryFrom::try_from(buf)?),
            BootSvcKind::MinBl0SecVerRequest => {
                Message::MinBl0SecVerRequest(TryFrom::try_from(buf)?)
            }
            BootSvcKind::MinBl0SecVerResponse => {
                Message::MinBl0SecVerResponse(TryFrom::try_from(buf)?)
            }
            BootSvcKind::NextBl0SlotRequest => Message::NextBl0SlotRequest(TryFrom::try_from(buf)?),
            BootSvcKind::NextBl0SlotResponse => {
                Message::NextBl0SlotResponse(TryFrom::try_from(buf)?)
            }
            BootSvcKind::PrimaryBl0SlotRequest => {
                Message::PrimaryBl0SlotRequest(TryFrom::try_from(buf)?)
            }
            BootSvcKind::PrimaryBl0SlotResponse => {
                Message::PrimaryBl0SlotResponse(TryFrom::try_from(buf)?)
            }
            BootSvcKind::UnlockOwnershipRequest => {
                Message::UnlockOwnershipRequest(TryFrom::try_from(buf)?)
            }
            BootSvcKind::UnlockOwnershipResponse => {
                Message::UnlockOwnershipResponse(TryFrom::try_from(buf)?)
            }
            BootSvcKind::ActivateOwnerRequest => {
                Message::ActivateOwnerRequest(TryFrom::try_from(buf)?)
            }
            BootSvcKind::ActivateOwnerResponse => {
                Message::ActivateOwnerResponse(TryFrom::try_from(buf)?)
            }
            _ => Message::Raw(buf.to_vec()),
        };

        Ok(BootSvc { header, message })
    }
}

impl BootSvc {
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let mut data = Vec::new();
        self.header.write(&mut data)?;
        match &self.message {
            Message::Empty(m) => m.write(&mut data)?,
            Message::MinBl0SecVerRequest(m) => m.write(&mut data)?,
            Message::MinBl0SecVerResponse(m) => m.write(&mut data)?,
            Message::NextBl0SlotRequest(m) => m.write(&mut data)?,
            Message::NextBl0SlotResponse(m) => m.write(&mut data)?,
            Message::PrimaryBl0SlotRequest(m) => m.write(&mut data)?,
            Message::PrimaryBl0SlotResponse(m) => m.write(&mut data)?,
            Message::UnlockOwnershipRequest(m) => m.write(&mut data)?,
            Message::UnlockOwnershipResponse(m) => m.write(&mut data)?,
            Message::ActivateOwnerRequest(m) => m.write(&mut data)?,
            Message::ActivateOwnerResponse(m) => m.write(&mut data)?,
            Message::Raw(m) => data.extend_from_slice(m.as_slice()),
        };
        let mut digest = Sha256::digest(&data[Header::HASH_LEN..]);
        digest.reverse();
        data[..Header::HASH_LEN].copy_from_slice(&digest);
        Ok(data)
    }

    pub fn min_bl0_sec_ver(ver: u32) -> Self {
        BootSvc {
            header: Header {
                digest: [0u32; 8],
                identifier: Header::IDENTIFIER,
                kind: BootSvcKind::MinBl0SecVerRequest,
                length: (Header::SIZE + MinBl0SecVerRequest::SIZE) as u32,
            },
            message: Message::MinBl0SecVerRequest(MinBl0SecVerRequest { ver }),
        }
    }

    pub fn next_boot_bl0_slot(slot: NextBootBl0) -> Self {
        BootSvc {
            header: Header {
                digest: [0u32; 8],
                identifier: Header::IDENTIFIER,
                kind: BootSvcKind::NextBl0SlotRequest,
                length: (Header::SIZE + NextBl0SlotRequest::SIZE) as u32,
            },
            message: Message::NextBl0SlotRequest(NextBl0SlotRequest {
                next_bl0_slot: slot,
            }),
        }
    }

    pub fn primary_bl0_slot(slot: BootDataSlot) -> Self {
        BootSvc {
            header: Header {
                digest: [0u32; 8],
                identifier: Header::IDENTIFIER,
                kind: BootSvcKind::PrimaryBl0SlotRequest,
                length: (Header::SIZE + PrimaryBl0SlotRequest::SIZE) as u32,
            },
            message: Message::PrimaryBl0SlotRequest(PrimaryBl0SlotRequest {
                primary_bl0_slot: slot,
            }),
        }
    }
}

impl TryFrom<&[u8]> for Header {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut val = Header::default();
        reader.read_u32_into::<LittleEndian>(&mut val.digest)?;
        val.identifier = reader.read_u32::<LittleEndian>()?;
        val.kind = BootSvcKind(reader.read_u32::<LittleEndian>()?);
        val.length = reader.read_u32::<LittleEndian>()?;
        Ok(val)
    }
}
impl Header {
    pub const SIZE: usize = 44;
    pub const IDENTIFIER: u32 = 0x43565342;
    const HASH_LEN: usize = 32;

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        for d in self.digest.iter() {
            dest.write_u32::<LittleEndian>(*d)?;
        }
        dest.write_u32::<LittleEndian>(self.identifier)?;
        dest.write_u32::<LittleEndian>(u32::from(self.kind))?;
        dest.write_u32::<LittleEndian>(self.length)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for Empty {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut val = Empty::default();
        val.payload.resize(64, 0);
        reader.read_u32_into::<LittleEndian>(&mut val.payload)?;
        Ok(val)
    }
}
impl Empty {
    pub const SIZE: usize = 256;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        for i in 0..64 {
            let p = self.payload.get(i).unwrap_or(&0);
            dest.write_u32::<LittleEndian>(*p)?;
        }
        Ok(())
    }
}

impl TryFrom<&[u8]> for MinBl0SecVerRequest {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(MinBl0SecVerRequest {
            ver: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl MinBl0SecVerRequest {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(self.ver)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for MinBl0SecVerResponse {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(MinBl0SecVerResponse {
            ver: reader.read_u32::<LittleEndian>()?,
            status: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl MinBl0SecVerResponse {
    pub const SIZE: usize = 8;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(self.ver)?;
        dest.write_u32::<LittleEndian>(self.status)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for NextBl0SlotRequest {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(NextBl0SlotRequest {
            next_bl0_slot: NextBootBl0(reader.read_u32::<LittleEndian>()?),
        })
    }
}
impl NextBl0SlotRequest {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.next_bl0_slot))?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for NextBl0SlotResponse {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(NextBl0SlotResponse {
            status: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl NextBl0SlotResponse {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(self.status)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for PrimaryBl0SlotRequest {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(PrimaryBl0SlotRequest {
            primary_bl0_slot: BootDataSlot(reader.read_u32::<LittleEndian>()?),
        })
    }
}
impl PrimaryBl0SlotRequest {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.primary_bl0_slot))?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for PrimaryBl0SlotResponse {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(PrimaryBl0SlotResponse {
            primary_bl0_slot: BootDataSlot(reader.read_u32::<LittleEndian>()?),
            status: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl PrimaryBl0SlotResponse {
    pub const SIZE: usize = 8;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.primary_bl0_slot))?;
        dest.write_u32::<LittleEndian>(self.status)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for UnlockOwnershipRequest {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut val = Self::default();
        val.unlock_mode = UnlockMode(reader.read_u32::<LittleEndian>()?);
        val.reserved.resize(Self::RESERVED_SIZE, 0);
        reader.read_exact(&mut val.reserved)?;
        val.nonce = reader.read_u64::<LittleEndian>()?;
        val.next_owner_key = EcdsaRawPublicKey::read(&mut reader).map_err(RescueError::Anyhow)?;
        val.signature = EcdsaRawSignature::read(&mut reader).map_err(RescueError::Anyhow)?;
        Ok(val)
    }
}
impl UnlockOwnershipRequest {
    pub const SIZE: usize = 8;
    const RESERVED_SIZE: usize = 18 * std::mem::size_of::<u32>();
    const SIGNATURE_OFFSET: usize = 148;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.unlock_mode))?;
        for i in 0..Self::RESERVED_SIZE {
            let p = self.reserved.get(i).unwrap_or(&0xFF);
            dest.write_all(std::slice::from_ref(p))?;
        }
        dest.write_u64::<LittleEndian>(self.nonce)?;
        self.next_owner_key.write(dest)?;
        self.signature.write(dest)?;
        Ok(())
    }

    pub fn set_next_owner_key(&mut self, key: &EcdsaPublicKey) -> Result<()> {
        self.next_owner_key = key.to_raw();
        Ok(())
    }

    pub fn sign(&mut self, key: &EcdsaPrivateKey) -> Result<()> {
        let mut data = Vec::new();
        self.write(&mut data)?;
        self.signature = key.digest_and_sign(&data[..Self::SIGNATURE_OFFSET])?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for UnlockOwnershipResponse {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(UnlockOwnershipResponse {
            status: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl UnlockOwnershipResponse {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(self.status)?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for ActivateOwnerRequest {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        let mut val = Self::default();
        val.primary_bl0_slot = BootDataSlot(reader.read_u32::<LittleEndian>()?);
        val.erase_previous = HardenedBool(reader.read_u32::<LittleEndian>()?);
        val.reserved.resize(Self::RESERVED_SIZE, 0);
        reader.read_exact(&mut val.reserved)?;
        val.nonce = reader.read_u64::<LittleEndian>()?;
        val.signature = EcdsaRawSignature::read(&mut reader).map_err(RescueError::Anyhow)?;
        Ok(val)
    }
}
impl ActivateOwnerRequest {
    pub const SIZE: usize = 8;
    const RESERVED_SIZE: usize = 33 * std::mem::size_of::<u32>();
    const SIGNATURE_OFFSET: usize = 148;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(u32::from(self.primary_bl0_slot))?;
        dest.write_u32::<LittleEndian>(u32::from(self.erase_previous))?;
        for i in 0..Self::RESERVED_SIZE {
            let p = self.reserved.get(i).unwrap_or(&0xFF);
            dest.write_all(std::slice::from_ref(p))?;
        }
        dest.write_u64::<LittleEndian>(self.nonce)?;
        self.signature.write(dest)?;
        Ok(())
    }

    pub fn sign(&mut self, key: &EcdsaPrivateKey) -> Result<()> {
        let mut data = Vec::new();
        self.write(&mut data)?;
        self.signature = key.digest_and_sign(&data[..Self::SIGNATURE_OFFSET])?;
        Ok(())
    }
}

impl TryFrom<&[u8]> for ActivateOwnerResponse {
    type Error = RescueError;
    fn try_from(buf: &[u8]) -> std::result::Result<Self, Self::Error> {
        let mut reader = std::io::Cursor::new(buf);
        Ok(ActivateOwnerResponse {
            status: reader.read_u32::<LittleEndian>()?,
        })
    }
}
impl ActivateOwnerResponse {
    pub const SIZE: usize = 4;
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u32::<LittleEndian>(self.status)?;
        Ok(())
    }
}
