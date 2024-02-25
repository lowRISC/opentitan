// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

extern crate serde;
extern crate serde_hjson;

use anyhow::{bail, Result};
use memoffset::offset_of;
use serde::Deserialize;

use std::fmt;
use std::fs;
use std::io::{self, Read};
use std::ops::Range;
use std::path::Path;

use std::{mem, ptr};

use crate::crypto::rsa::RsaPrivateKey;
use crate::crypto::sha256;
use crate::util::parse_int::ParseInt;

// RV32 NOP (addi, x0, x0, 0)
const RV32_NOP: u32 = 0x00000013;

// RSA-3072 signature length in bytes
const RSA_SIGNATURE_LEN_BYTES: usize = 3072 / 8;

// At most 32 match descriptors per patch
const N_MATCH_DESCRIPTORS: usize = 32;

// Patch match table size
const PATCH_MATCH_TABLE_SIZE: usize =
    N_MATCH_DESCRIPTORS * mem::size_of::<RomPatchMatchDescriptor>();

// The code section offset from the patch start
const PATCH_CODE_SECTION_OFFSET: usize = mem::size_of::<RomPatchHeader>() + PATCH_MATCH_TABLE_SIZE;

#[allow(dead_code)]
enum MultiBitBool {
    Bool4True = 0x6,
    Bool4False = 0x9,
}

#[derive(Deserialize, Debug)]
struct RomPatchSubRoutineHjson {
    base_addr: String,
    code: Vec<String>,
}

#[derive(Deserialize, Debug)]
struct RomPatchRegionHjson {
    match_addr: String,
    locked: bool,
    patch_code: Vec<String>,
    sub_routines: Option<Vec<RomPatchSubRoutineHjson>>,
}

#[derive(Deserialize, Debug)]
struct RomPatchHjson {
    revision: u8,
    base_addr: String,
    regions: Vec<RomPatchRegionHjson>,
}

#[derive(Deserialize, Debug)]
pub struct RomPatchPartitionHjson {
    patches: Vec<RomPatchHjson>,
}

#[derive(Copy, Clone, Debug, Default)]
#[allow(dead_code)]
#[repr(packed)]
struct RomPatchMatchDescriptor {
    match_base: u32,
    remap_base: u32,
}

impl RomPatchMatchDescriptor {
    fn from_hjson(remap_base: u32, region: &RomPatchRegionHjson) -> Result<Self> {
        let match_addr = u32::from_str(&region.match_addr)?;

        let size_dwords = (region.patch_code.len() as u32) & 0xf;
        let locked = if region.locked { 1 << 31 } else { 0 };

        let match_address = match_addr & 0x7ffffff;
        let match_base = locked | (size_dwords << 27) | match_address;

        Ok(RomPatchMatchDescriptor {
            match_base,
            remap_base,
        })
    }

    fn match_addr(&self) -> u32 {
        self.match_base & 0xffff
    }

    fn remap_addr(&self) -> u32 {
        self.remap_base
    }

    fn locked(&self) -> bool {
        (self.match_base >> 31) != 0
    }

    fn size(&self) -> u8 {
        ((self.match_base >> 27) & 0xf) as u8
    }

    fn enabled(&self) -> bool {
        self.match_base != 0 && self.remap_base != 0
    }
}

impl fmt::Display for RomPatchMatchDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "\tMatch address {:#04x}", self.match_addr())?;
        writeln!(f, "\tRemap address {:#04x}", self.remap_addr())?;
        write!(
            f,
            "\tPatch size {:?} Locked {:?} ",
            self.size(),
            self.locked()
        )
    }
}

#[derive(Default, Clone, Copy, Debug)]
#[allow(dead_code)]
#[repr(packed)]
struct RomPatchHeader {
    meta: u8,
    size: u16,
    revision: u8,
}

impl Read for RomPatchHeader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let raw_header = self as *const _ as *const u8;
        let header_size = mem::size_of::<RomPatchHeader>();

        if buf.len() < header_size {
            return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput));
        }

        unsafe {
            ptr::copy_nonoverlapping(raw_header, buf.as_mut_ptr(), header_size);
        }

        Ok(header_size)
    }
}

impl fmt::Display for RomPatchHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let unaligned = std::ptr::addr_of!(self.size);
        let size = unsafe { std::ptr::read_unaligned(unaligned) };
        write!(
            f,
            "\tMeta {:#x} Revision {:?} Size {:?} DWORDs",
            self.meta, self.revision, size
        )
    }
}

struct RomPatchSubRoutine {
    base_addr: u32,
    offset: usize,
    code: Vec<u32>,
}

impl RomPatchSubRoutine {
    fn from_hjson(routine: &RomPatchSubRoutineHjson, patch_base_addr: u32) -> Result<Self> {
        let base_addr = u32::from_str(&routine.base_addr)?;
        if base_addr < patch_base_addr {
            bail!(
                "Invalid subroutine base addr {:#x} < {:#x} ",
                base_addr,
                patch_base_addr
            );
        }

        let mut code = vec![];
        for insn in &routine.code {
            let insn_hex = u32::from_str(insn)?;
            code.push(insn_hex);
        }

        let offset = PATCH_CODE_SECTION_OFFSET + (base_addr - patch_base_addr) as usize;

        Ok(Self {
            base_addr,
            offset,
            code,
        })
    }

    fn len(&self) -> usize {
        self.code.len() * 4
    }

    fn offset(&self) -> usize {
        self.offset
    }

    fn range(&self) -> Range<u32> {
        Range {
            start: self.base_addr,
            end: self.base_addr + (self.code.len() as u32 * 4),
        }
    }
}

impl fmt::Display for RomPatchSubRoutine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let range = self.range();
        write!(
            f,
            "\tBase address {:#04x} Range [{:#04x}:{:#04x}]",
            self.base_addr, range.start, range.end
        )
    }
}

impl Read for RomPatchSubRoutine {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() < self.len() {
            return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput));
        }

        let mut buf_offset = 0;

        for insn in &self.code {
            let insn_bytes = insn.to_le_bytes();
            let raw_insn_bytes = &insn_bytes as *const _ as *const u8;
            unsafe {
                ptr::copy_nonoverlapping(raw_insn_bytes, buf[buf_offset..].as_mut_ptr(), 4);
            }
            buf_offset += 4;
        }

        Ok(self.len())
    }
}

struct RomPatch<'a> {
    header: RomPatchHeader,
    size: usize,
    code_offset: usize,
    signature_offset: usize,
    base_addr: u32,
    match_table: [RomPatchMatchDescriptor; N_MATCH_DESCRIPTORS],
    patch_code: Vec<u32>,
    sub_routines: Vec<RomPatchSubRoutine>,
    signature_key: &'a RsaPrivateKey,
}

impl<'a> RomPatch<'a> {
    fn from_hjson(patch: &RomPatchHjson, signature_key: &'a RsaPrivateKey) -> Result<Self> {
        let meta = MultiBitBool::Bool4True as u8; // Lock Valid = 1, Program Start = 0
        let base_addr = u32::from_str(&patch.base_addr)?;
        let mut remap_addr = base_addr;
        let mut match_table: [RomPatchMatchDescriptor; N_MATCH_DESCRIPTORS] = Default::default();
        let mut patch_code = vec![];
        let mut sub_routines = vec![];

        for (index, region) in patch.regions.iter().enumerate() {
            let match_pair = RomPatchMatchDescriptor::from_hjson(remap_addr, region)?;
            match_table[index] = match_pair;
            remap_addr += (region.patch_code.len() as u32) * 4;

            for insn in &region.patch_code {
                let insn_hex = u32::from_str(insn)?;
                patch_code.push(insn_hex);
            }

            if let Some(sub_routines_hjson) = &region.sub_routines {
                for sub_routine_hjson in sub_routines_hjson {
                    let sub_routine = RomPatchSubRoutine::from_hjson(sub_routine_hjson, base_addr)?;
                    sub_routines.push(sub_routine);
                }
            }
        }

        let mut code_addr_end = base_addr + ((patch_code.len() as u32) * 4);
        for s in &sub_routines {
            code_addr_end = std::cmp::max(code_addr_end, s.range().end);
        }

        let code_len = (code_addr_end - base_addr) as usize;
        let patch_size = mem::size_of::<RomPatchHeader>()
            + (N_MATCH_DESCRIPTORS * mem::size_of::<RomPatchMatchDescriptor>())
            + code_len
            + RSA_SIGNATURE_LEN_BYTES;

        let header = RomPatchHeader {
            meta,
            size: (patch_size >> 2) as u16,
            revision: patch.revision,
        };

        Ok(RomPatch {
            header,
            size: patch_size,
            code_offset: PATCH_CODE_SECTION_OFFSET,
            signature_offset: PATCH_CODE_SECTION_OFFSET + code_len,
            base_addr,
            match_table,
            patch_code,
            sub_routines,
            signature_key,
        })
    }

    fn code_offset(&self) -> usize {
        self.code_offset
    }

    fn signature_offset(&self) -> usize {
        self.signature_offset
    }

    fn code_len(&self) -> usize {
        self.signature_offset() - self.code_offset()
    }

    fn len(&self) -> usize {
        self.size
    }

    fn validate(&self) -> Result<()> {
        Ok(())
    }
}

impl<'a> fmt::Display for RomPatch<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Code range [{:#x}:{:#x}]",
            self.base_addr,
            self.base_addr + self.code_len() as u32
        )?;
        writeln!(f, "Header\n{}", self.header)?;
        for (i, m) in self.match_table.iter().enumerate() {
            if !m.enabled() {
                continue;
            }
            writeln!(f, "Match descriptor #{}: \n{}", i, m)?;
        }
        for (i, s) in self.sub_routines.iter().enumerate() {
            writeln!(f, "Sub routine #{}: \n{}", i, s)?;
        }
        writeln!(f, "Remapped code {:?} bytes", self.patch_code.len() * 4)?;
        writeln!(f, "Size {:?} bytes", self.len())?;
        writeln!(f, "\tHeader {:?} bytes", mem::size_of::<RomPatchHeader>())?;
        writeln!(
            f,
            "\tDescriptors {:?} bytes",
            mem::size_of_val(&self.match_table)
        )?;
        writeln!(f, "\tCode {:?} bytes", self.code_len())?;
        writeln!(f, "\tSignature {:?}", RSA_SIGNATURE_LEN_BYTES)
    }
}

impl<'a> Read for RomPatch<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.len() < self.size {
            return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput));
        }

        let mut buf_offset = self.header.read(buf)?;
        let match_table_size = PATCH_MATCH_TABLE_SIZE;
        let raw_match_table = &self.match_table as *const _ as *const u8;
        unsafe {
            ptr::copy_nonoverlapping(
                raw_match_table,
                buf[buf_offset..].as_mut_ptr(),
                match_table_size,
            );
        }

        /* Fill the rest of the patch with NOPs */
        let nop_bytes = RV32_NOP.to_le_bytes();
        let mut offset = 0;
        let code_section = &mut buf[self.code_offset()..self.code_offset() + self.code_len()];
        while offset + 4 < code_section.len() {
            unsafe {
                ptr::copy_nonoverlapping(
                    nop_bytes.as_ptr(),
                    code_section[offset..].as_mut_ptr(),
                    4,
                );
            }

            offset += 4;
        }

        /* Copy the whole patch section */
        buf_offset = self.code_offset();
        for insn in &self.patch_code {
            let insn_bytes = insn.to_le_bytes();
            let raw_insn_bytes = &insn_bytes as *const _ as *const u8;
            unsafe {
                ptr::copy_nonoverlapping(raw_insn_bytes, buf[buf_offset..].as_mut_ptr(), 4);
            }
            buf_offset += 4;
        }

        /* Copy all subroutines, at their respective offsets */
        for sub_routine in self.sub_routines.iter_mut() {
            if sub_routine.read(&mut buf[sub_routine.offset()..])? != sub_routine.len() {
                return Err(std::io::Error::new(
                    io::ErrorKind::Other,
                    "Subroutine read failure".to_string(),
                ));
            }
        }

        /*
         * Compute the patch signature.
         * The first byte (The header meta data, lock valid and program start)
         * is not part of the signed payload as it can be toggled by the patch
         * loader.
         */
        let signed_payload = &buf[offset_of!(RomPatchHeader, size)..self.signature_offset()];
        let digest = sha256::sha256(signed_payload);
        let signature: &[u8] = &self
            .signature_key
            .sign(&digest)
            .map_err(|e| std::io::Error::new(io::ErrorKind::Other, e.to_string()))?
            .to_le_bytes()[..];

        /* Copy the signature */
        unsafe {
            ptr::copy_nonoverlapping(
                signature.as_ptr(),
                buf[self.signature_offset()..].as_mut_ptr(),
                RSA_SIGNATURE_LEN_BYTES,
            );
        }

        Ok(self.len())
    }
}

pub struct RomPatchPartition<'a> {
    size: usize,
    patches: Vec<RomPatch<'a>>,
}

impl<'a> RomPatchPartition<'a> {
    pub fn new(hjson_file: &Path, key: &'a RsaPrivateKey) -> Result<Self> {
        let hjson_text = fs::read_to_string(hjson_file)?;
        let patch_partition_hjson: RomPatchPartitionHjson = deser_hjson::from_str(&hjson_text)?;

        let mut patches = vec![];
        let mut size = 0;

        for p in &patch_partition_hjson.patches {
            let patch = RomPatch::from_hjson(p, key)?;
            patch.validate()?;

            size += patch.len();
            patches.push(patch);
        }

        Ok(RomPatchPartition { size, patches })
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl<'a> fmt::Display for RomPatchPartition<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, p) in self.patches.iter().enumerate() {
            write!(f, "Patch #{}:\n{}", i, p)?;
        }

        Ok(())
    }
}

impl<'a> Read for RomPatchPartition<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut buf_offset = 0;

        if buf.len() < self.size {
            return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput));
        }

        for p in &mut self.patches {
            buf_offset += p.read(&mut buf[buf_offset..])?;
        }

        Ok(self.size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;

    #[test]
    fn test_rom_patch_match_descriptor_deser() -> Result<()> {
        let mut match_addr = 0x8940;
        let remap_addr = 0x1000;
        let hjson = format!(
            r#"{{
             match_addr: {:#x}
             locked: true
             patch_code: [
                 0x05a50510
                 0x05a50511
                 0x05a50512
                 0x05a50513
             ]
        }}"#,
            match_addr
        );

        let region = deser_hjson::from_str(&hjson)?;
        let match_desc = RomPatchMatchDescriptor::from_hjson(remap_addr, &region)?;
        let size = match_desc.size() as u32 * 4;
        match_addr = (match_addr & !(size - 1)) | ((size - 1) >> 1);

        assert_eq!(match_desc.remap_addr(), remap_addr);
        assert_eq!(match_desc.match_addr(), match_addr);
        assert_eq!(match_desc.locked(), true);
        assert_eq!(match_desc.size(), 4);

        Ok(())
    }

    #[test]
    fn test_rom_patch_sub_routine_deser() -> Result<()> {
        let patch_base_addr = 0x1000;
        let base_addr = 0x1010;
        let hjson = format!(
            r#"{{
             base_addr: {:#x}
             code: [
                 0x05a50510
                 0x05a50511
                 0x05a50512
                 0x05a50513
             ]
        }}"#,
            base_addr
        );

        let sub_routine_hjson = deser_hjson::from_str(&hjson)?;
        let sub_routine = RomPatchSubRoutine::from_hjson(&sub_routine_hjson, patch_base_addr)?;
        assert_eq!(sub_routine.base_addr, base_addr);
        assert_eq!(sub_routine.code.len(), 4);
        assert_eq!(
            sub_routine.range(),
            Range {
                start: base_addr,
                end: base_addr + (sub_routine.code.len() as u32 * 4)
            }
        );
        assert_eq!(
            sub_routine.offset(),
            PATCH_CODE_SECTION_OFFSET + (base_addr - patch_base_addr) as usize
        );

        Ok(())
    }

    #[test]
    fn test_rom_patch_deser() -> Result<()> {
        let sram_base_addr = 0x10000000;
        let routine_base_addr = 0x10001000;
        let match_addr = 0x8940;
        let revision = 88;
        let hjson = format!(
            r#"{{
                   revision: {}
                   base_addr: {:#x}
                   regions: [
                      {{
                          match_addr: {:#x}
                          locked: true
                          patch_code: [
                                   0x05a50510
                                   0x05a50511
                                   0x05a50512
                                   0x05a50513
                               ]
                          sub_routines: [
                              {{
                                   base_addr: {:#x}
                                   code: [
                                        0x53400593
                                        0x00c60563
                                        0x548a0596
                                        0x0d050563
                                  ]
                              }}
                          ]
                      }}
                   ]
               }}"#,
            revision, sram_base_addr, match_addr, routine_base_addr
        );

        let key = RsaPrivateKey::from_pkcs8_der_file(testdata!("test.der"))?;
        let patch_hjson = deser_hjson::from_str(&hjson)?;
        let patch = RomPatch::from_hjson(&patch_hjson, &key)?;

        assert_eq!(patch.header.revision, revision);
        assert_eq!(patch.sub_routines.len(), 1);
        assert_eq!(patch.patch_code.len(), 4);
        assert_eq!(patch.match_table[0].enabled(), true);
        assert_eq!(patch.match_table[1].enabled(), false);
        let size = (patch.patch_code.len() * 4) as u32;
        assert_eq!(
            patch.match_table[0].match_addr(),
            (match_addr & !(size - 1)) | ((size - 1) >> 1)
        );

        assert_eq!(patch.code_offset(), PATCH_CODE_SECTION_OFFSET);
        assert_eq!(
            patch.signature_offset(),
            PATCH_CODE_SECTION_OFFSET + patch.code_len()
        );
        assert_eq!(
            patch.sub_routines[0].offset(),
            PATCH_CODE_SECTION_OFFSET + (routine_base_addr - sram_base_addr) as usize
        );

        Ok(())
    }

    #[test]
    fn test_rom_patch_read() -> Result<()> {
        let sram_base_addr = 0x10000000;
        let routine_base_addr = 0x10000100;
        let match_addr = 0x8940;
        let revision = 88;
        let first_subroutine_insn = 0x53400593;
        let first_patch_code_insn = 0x05a50510;
        let hjson = format!(
            r#"{{
                   revision: {}
                   base_addr: {:#x}
                   regions: [
                      {{
                          match_addr: {:#x}
                          locked: true
                          patch_code: [
                                   {:#x}
                                   0x05a50511
                                   0x05a50512
                                   0x05a50513
                               ]
                          sub_routines: [
                              {{
                                   base_addr: {:#x}
                                   code: [
                                        {:#x}
                                        0x00c60563
                                        0x548a0596
                                        0x0d050563
                                  ]
                              }}
                          ]
                      }}
                   ]
               }}"#,
            revision,
            sram_base_addr,
            match_addr,
            first_patch_code_insn,
            routine_base_addr,
            first_subroutine_insn
        );

        let key = RsaPrivateKey::from_pkcs8_der_file(testdata!("test.der"))?;
        let patch_hjson = deser_hjson::from_str(&hjson)?;

        let mut patch = RomPatch::from_hjson(&patch_hjson, &key)?;
        let mut buffer = vec![0_u8; 2048];

        assert_eq!(patch.sub_routines.len(), 1);
        assert_eq!(patch.read(&mut buffer)?, patch.len());

        let subroutine_insn = u32::from_le_bytes(
            buffer[patch.sub_routines[0].offset()..patch.sub_routines[0].offset() + 4]
                .try_into()
                .unwrap(),
        );
        assert_eq!(subroutine_insn, first_subroutine_insn);

        let patch_insn = u32::from_le_bytes(
            buffer[patch.code_offset()..patch.code_offset() + 4]
                .try_into()
                .unwrap(),
        );
        assert_eq!(patch_insn, first_patch_code_insn);

        Ok(())
    }

    #[test]
    fn test_rom_patch_header_read() -> Result<()> {
        let mut header = RomPatchHeader {
            meta: 0x78,
            size: 0x100,
            revision: 1,
        };
        let expected_blob: [u8; 4] = [0x78, 0x00, 0x01, 0x01];

        let mut buf = vec![0u8; 4];
        assert_eq!(header.read(&mut buf)?, 4);
        assert_eq!(buf, expected_blob);

        Ok(())
    }

    #[test]
    fn test_rom_patch_header_read_short_buffer() -> Result<()> {
        let mut header = RomPatchHeader {
            meta: 0x78,
            size: 0x100,
            revision: 1,
        };

        let mut buf = vec![0u8; 2];
        assert!(header.read(&mut buf).is_err());

        Ok(())
    }
}
