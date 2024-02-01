// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::Serialize;
use serde_annotate::Annotate;
use sha2::{Digest, Sha256};
use std::convert::TryFrom;
use std::io::Write;

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

    pub enum BootSvcKind: u32 [default = Self::Unknown] {
        Unknown = 0,
        Empty = 0xb4594546,
        MinBl0SecVerRequest = 0xdac59e6e,
        MinBl0SecVerResponse = 0x756385f1,
        NextBl0SlotRequest = 0xe1edf546,
        NextBl0SlotResponse = 0x657051be,
        PrimaryBl0SlotRequest = 0x3d6c47b8,
        PrimaryBl0SlotResponse = 0xf2a4a609,
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
    MinBl0SecVerResponse(MinBl0SecVerResponse),
    NextBl0SlotResponse(NextBl0SlotResponse),
    PrimaryBl0SlotResponse(PrimaryBl0SlotResponse),
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
