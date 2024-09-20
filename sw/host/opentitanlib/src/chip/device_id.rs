// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use serde::Serialize;
use serde_annotate::Annotate;
use std::io::{Read, Write};

#[derive(Debug, Default, Serialize, Annotate)]
pub struct DeviceId {
    #[annotate(format=hex)]
    creator: u16,
    #[annotate(format=hex)]
    product: u16,
    #[annotate(format=hex)]
    id: u64,
    #[annotate(format=hex)]
    crc32: u32,
    #[annotate(format=hex)]
    sku_specific: [u32; 4],
}

impl DeviceId {
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let creator = src.read_u16::<LittleEndian>()?;
        let product = src.read_u16::<LittleEndian>()?;
        let id = src.read_u64::<LittleEndian>()?;
        let crc32 = src.read_u32::<LittleEndian>()?;
        let mut sku_specific = [0u32; 4];
        src.read_u32_into::<LittleEndian>(&mut sku_specific)?;
        Ok(Self {
            creator,
            product,
            id,
            crc32,
            sku_specific,
        })
    }

    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        dest.write_u16::<LittleEndian>(self.creator)?;
        dest.write_u16::<LittleEndian>(self.product)?;
        dest.write_u64::<LittleEndian>(self.id)?;
        dest.write_u32::<LittleEndian>(self.crc32)?;
        for sku_specific in &self.sku_specific {
            dest.write_u32::<LittleEndian>(*sku_specific)?;
        }
        Ok(())
    }
}
