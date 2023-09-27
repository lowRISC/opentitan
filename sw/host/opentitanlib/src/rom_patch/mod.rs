// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::bail;
use anyhow::ensure;
use anyhow::Error;
use anyhow::Result;
use memoffset::offset_of;
use serde::Deserialize;
use serde::Deserializer;
use zerocopy::AsBytes;
use zerocopy::FromBytes;
use zerocopy::FromZeroes;

use std::fs;
use std::io;
use std::io::Write;
use std::mem;
use std::path::Path;

use crate::chip::boolean::MultiBitBool4;
use crate::crypto::ecdsa::EcdsaPrivateKey;
use crate::crypto::sha256;
use crate::util::file::ToWriter;
use crate::util::parse_int::ParseInt;

// RV32 NOP (addi, x0, x0, 0)
const RV32_NOP: u32 = 0x00000013;

// ECDSA P256 signature length in bytes
const ECDSA_SIGNATURE_LEN_BYTES: usize = 64;

// At most 32 match descriptors per patch
pub const N_MATCH_DESCRIPTORS: usize = 32;

// Patch match table size
const PATCH_MATCH_TABLE_SIZE: usize =
    N_MATCH_DESCRIPTORS * mem::size_of::<RomPatchMatchDescriptor>();

// The code section offset from the patch start
const PATCH_CODE_SECTION_OFFSET: usize = mem::size_of::<RomPatchHeader>() + PATCH_MATCH_TABLE_SIZE;

fn deserialize_hex_u32<'de, D>(deserializer: D) -> Result<u32, D::Error>
where
    D: Deserializer<'de>,
{
    let s: String = Deserialize::deserialize(deserializer)?;
    u32::from_str_radix(s.trim_start_matches("0x"), 16).map_err(serde::de::Error::custom)
}

fn deserialize_hex_usize<'de, D>(deserializer: D) -> Result<usize, D::Error>
where
    D: Deserializer<'de>,
{
    let s: String = Deserialize::deserialize(deserializer)?;
    usize::from_str_radix(s.trim_start_matches("0x"), 16).map_err(serde::de::Error::custom)
}

#[derive(Deserialize, Debug)]
struct RomPatchSubRoutineHjson {
    #[serde(deserialize_with = "deserialize_hex_usize")]
    offset: usize,
    code: Vec<String>,
}

#[derive(Deserialize, Debug, Default)]
struct RomPatchRegionHjson {
    #[serde(deserialize_with = "deserialize_hex_u32")]
    match_addr: u32,
    locked: bool,
    patch_code: Vec<String>,
    #[serde(default)]
    sub_routines: Vec<RomPatchSubRoutineHjson>,
}

#[derive(Deserialize, Debug)]
struct RomPatchHjson {
    revision: u8,
    #[serde(deserialize_with = "deserialize_hex_u32")]
    base_addr: u32,
    regions: Vec<RomPatchRegionHjson>,
}

#[derive(Deserialize, Debug)]
pub struct RomPatchPartitionHjson {
    patches: Vec<RomPatchHjson>,
}

#[derive(AsBytes, Default, Clone, Copy, Debug)]
#[repr(packed, C)]
struct RomPatchHeader {
    meta: u8,
    size: u16,
    revision: u8,
}

#[derive(AsBytes, Copy, Clone, Debug, Default)]
#[repr(packed, C)]
struct RomPatchMatchDescriptor {
    match_base: u32,
    remap_base: u32,
}

// Patch locked field position in the match descriptor.
const PATCH_LOCKED_FIELD_SHIFT: usize = 31;

// Patch size field position in the match descriptor.
const PATCH_SIZE_FIELD_SHIFT: usize = 27;
const PATCH_SIZE_FIELD_WIDTH: usize = 4;
const PATCH_SIZE_FIELD_MASK: u32 = (1 << PATCH_SIZE_FIELD_WIDTH) - 1;

// Patch match address in the match descriptor.
const PATCH_MATCH_ADDR_FIELD_WIDTH: usize = 27;
const PATCH_MATCH_ADDR_FIELD_MASK: u32 = (1 << PATCH_MATCH_ADDR_FIELD_WIDTH) - 1;

impl RomPatchMatchDescriptor {
    fn from_hjson(remap_base: u32, region: &RomPatchRegionHjson) -> Result<Self> {
        let match_addr = region.match_addr;
        let patch_code_size_words = region.patch_code.len();

        let size_dwords = match patch_code_size_words {
            1 | 2 | 4 | 8 => (patch_code_size_words as u32) & PATCH_SIZE_FIELD_MASK,
            _ => bail!("Invalid ROM patch region code size {patch_code_size_words}"),
        };
        let locked = (region.locked as u32) << PATCH_LOCKED_FIELD_SHIFT;

        let match_address = if match_addr <= PATCH_MATCH_ADDR_FIELD_MASK {
            match_addr & PATCH_MATCH_ADDR_FIELD_MASK
        } else {
            bail!("Invalid ROM patch match address {match_addr}")
        };

        let match_base = locked | (size_dwords << PATCH_SIZE_FIELD_SHIFT) | match_address;

        Ok(RomPatchMatchDescriptor {
            match_base,
            remap_base,
        })
    }
}

#[derive(AsBytes, Copy, Clone, Debug)]
#[repr(packed, C)]
struct RomPatchMatchTable<const N: usize> {
    table: [RomPatchMatchDescriptor; N],
}

impl<const N: usize> RomPatchMatchTable<N> {
    fn from_hjson(base_addr: u32, regions: &[RomPatchRegionHjson]) -> Result<Self> {
        let mut table: [RomPatchMatchDescriptor; N] = [RomPatchMatchDescriptor::default(); N];
        let mut remap_addr = base_addr;

        assert!(N >= regions.len());

        for (index, region) in regions.iter().enumerate() {
            let match_pair = RomPatchMatchDescriptor::from_hjson(remap_addr, region)?;
            table[index] = match_pair;
            remap_addr += (region.patch_code.len() as u32) * mem::size_of::<u32>() as u32;
        }

        Ok(Self { table })
    }
}

#[derive(Clone, Debug, Default)]
struct RomPatchCode {
    code: Vec<u32>,
}

impl RomPatchCode {
    fn from_hjson(regions: &[RomPatchRegionHjson]) -> Result<Self> {
        let mut code_size_words = regions.iter().map(|r| r.patch_code.len()).sum();

        // Compute the overall code size for the patch.
        code_size_words = regions
            .iter()
            .flat_map(|region| region.sub_routines.iter())
            .map(|s| (s.offset >> 2) + s.code.len())
            .fold(code_size_words, std::cmp::max);

        // Copy the patch code itself.
        let mut code = vec![RV32_NOP; code_size_words];
        for (code_index, insn) in regions
            .iter()
            .flat_map(|region| region.patch_code.iter())
            .enumerate()
        {
            let insn_hex = u32::from_str(insn.trim_end_matches(','))?;
            code[code_index] = insn_hex;
        }

        // Copy all subroutines.
        regions
            .iter()
            .flat_map(|region| &region.sub_routines)
            .try_for_each(|sub_routine| {
                let offset_words = sub_routine.offset >> 2;
                sub_routine
                    .code
                    .iter()
                    .enumerate()
                    .try_for_each(|(index, insn)| {
                        let insn_hex = u32::from_str(insn.trim_end_matches(','))?;
                        code[offset_words + index] = insn_hex;
                        Ok::<(), Error>(())
                    })?;
                Ok::<(), Error>(())
            })?;

        Ok(Self { code })
    }

    fn len_bytes(&self) -> usize {
        self.code.len() * mem::size_of::<u32>()
    }

    fn as_bytes(&self) -> &[u8] {
        let ptr = self.code.as_ptr();
        let len = self.code.len() * std::mem::size_of::<u32>();

        unsafe { std::slice::from_raw_parts(ptr as *const u8, len) }
    }
}

#[repr(packed, C)]
#[derive(Debug, Clone, FromBytes, FromZeroes, AsBytes)]
pub struct RomPatchSig {
    signature: [u8; ECDSA_SIGNATURE_LEN_BYTES],
}

impl Default for RomPatchSig {
    fn default() -> Self {
        Self {
            signature: [0; ECDSA_SIGNATURE_LEN_BYTES],
        }
    }
}

#[derive(Debug, Clone)]
struct RomPatch<const N: usize> {
    header: RomPatchHeader,
    match_table: RomPatchMatchTable<N>,
    code: RomPatchCode,
    signature: RomPatchSig,
}

impl<const N: usize> ToWriter for RomPatch<N> {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        w.write_all(self.header.as_bytes())?;
        w.write_all(self.match_table.as_bytes())?;
        w.write_all(self.code.as_bytes())?;
        w.write_all(self.signature.as_bytes())?;

        Ok(())
    }
}

#[repr(transparent)]
#[derive(Debug, Copy, Clone, FromBytes, FromZeroes, AsBytes)]
struct U32Wrapper(u32);

impl<const N: usize> RomPatch<N> {
    fn from_hjson(patch: &RomPatchHjson, signature_key: &EcdsaPrivateKey) -> Result<Self> {
        let meta: u8 = MultiBitBool4::True.into(); // Lock Valid = 1, Program Start = 0
        let match_table = RomPatchMatchTable::from_hjson(patch.base_addr, &patch.regions)?;
        let code = RomPatchCode::from_hjson(&patch.regions)?;
        let code_len_bytes = code.len_bytes();
        let patch_size_bytes = mem::size_of::<RomPatchHeader>()
            + (N_MATCH_DESCRIPTORS * mem::size_of::<RomPatchMatchDescriptor>())
            + code_len_bytes
            + ECDSA_SIGNATURE_LEN_BYTES;
        ensure!(
            (patch_size_bytes % mem::size_of::<u32>()) == 0,
            "ROM patch size must be a multiple of 4"
        );

        let header = RomPatchHeader {
            meta,
            size: (patch_size_bytes / mem::size_of::<u32>()) as u16,
            revision: patch.revision,
        };

        /* Generate the patch signature */
        let mut patch_bytes = vec![];
        let code_bytes = code.as_bytes();
        patch_bytes.extend_from_slice(header.as_bytes());
        patch_bytes.extend_from_slice(match_table.as_bytes());
        patch_bytes.extend_from_slice(code_bytes);

        /* The signed payload does not include the header meta data */
        let signature_offset = PATCH_CODE_SECTION_OFFSET + code_len_bytes;
        let signed_payload = &patch_bytes[offset_of!(RomPatchHeader, size)..signature_offset];

        /* Generate the digest and sign it with the provided private key */
        let digest = sha256::sha256(signed_payload);
        let signature = RomPatchSig::read_from(
            &signature_key
                .sign(&digest)
                .map_err(|e| std::io::Error::new(io::ErrorKind::Other, e.to_string()))?
                .to_vec()
                .map_err(|e| std::io::Error::new(io::ErrorKind::Other, e.to_string()))?,
        )
        .ok_or(std::io::Error::new(
            io::ErrorKind::InvalidInput,
            "Could not sign ROM patch",
        ))?;

        Ok(RomPatch {
            header,
            match_table,
            code,
            signature,
        })
    }

    fn as_vec(&self) -> Result<Vec<u32>> {
        let mut patch_bytes = vec![];
        let code_bytes = self.code.as_bytes();
        patch_bytes.extend_from_slice(self.header.as_bytes());
        patch_bytes.extend_from_slice(self.match_table.as_bytes());
        patch_bytes.extend_from_slice(code_bytes);
        patch_bytes.extend_from_slice(self.signature.as_bytes());

        let mut patch_words = Vec::with_capacity(patch_bytes.len() / std::mem::size_of::<u32>());

        for chunk in patch_bytes.chunks_exact(std::mem::size_of::<u32>()) {
            let word = U32Wrapper::read_from(chunk).ok_or(std::io::Error::new(
                io::ErrorKind::InvalidData,
                "Failed to convert a ROM patch to a u32 vector",
            ))?;

            patch_words.push(word.0);
        }

        Ok(patch_words)
    }
}

#[derive(Debug, Clone)]
pub struct RomPatchPartition<const N: usize> {
    patches: Vec<RomPatch<N>>,
}

impl<const N: usize> RomPatchPartition<N> {
    pub fn new(hjson_file: &Path, key: &EcdsaPrivateKey) -> Result<Self> {
        let hjson_text = fs::read_to_string(hjson_file)?;
        let patch_partition_hjson: RomPatchPartitionHjson = deser_hjson::from_str(&hjson_text)?;

        RomPatchPartition::from_hjson(&patch_partition_hjson, key)
    }

    pub fn from_hjson(
        patch_partition_hjson: &RomPatchPartitionHjson,
        key: &EcdsaPrivateKey,
    ) -> Result<Self> {
        let mut patches = vec![];

        for p in &patch_partition_hjson.patches {
            patches.push(RomPatch::from_hjson(p, key)?);
        }

        Ok(RomPatchPartition { patches })
    }

    pub fn as_vec(&self) -> Result<Vec<u32>> {
        let mut patch_words = vec![];
        for patch in &self.patches {
            patch_words.append(&mut patch.as_vec()?);
        }

        Ok(patch_words)
    }
}

impl<const N: usize> ToWriter for RomPatchPartition<N> {
    fn to_writer(&self, w: &mut impl Write) -> Result<()> {
        for patch in &self.patches {
            patch.to_writer(w)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;

    struct RomPatchConfig {
        base_addr: usize,
        match_addr: usize,
        routine_offset: usize,
        revision: u8,
        patch_code: [u32; 4],
        sub_routine: [u32; 4],
    }

    impl RomPatchConfig {
        fn header(&self) -> u32 {
            let header = RomPatchHeader {
                meta: MultiBitBool4::True.into(),
                size: (self.patch_size_bytes() / std::mem::size_of::<u32>()) as u16,
                revision: self.revision,
            };

            let bytes = header.as_bytes();
            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
        }

        fn code_size_bytes(&self) -> usize {
            self.routine_offset + (self.sub_routine.len() * std::mem::size_of::<u32>())
        }

        fn patch_size_bytes(&self) -> usize {
            mem::size_of::<RomPatchHeader>()
                + PATCH_MATCH_TABLE_SIZE
                + self.code_size_bytes()
                + ECDSA_SIGNATURE_LEN_BYTES
        }

        fn first_insn(&self) -> u32 {
            *self.patch_code.first().unwrap()
        }

        fn last_insn(&self) -> u32 {
            *self.sub_routine.last().unwrap()
        }
    }

    static FIRST_CONFIG: RomPatchConfig = RomPatchConfig {
        base_addr: 0x10000000,
        match_addr: 0x8940,
        routine_offset: 0x1000,
        revision: 88,
        patch_code: [0x05a50510, 0x05a50511, 0x05a50512, 0x05a50513],
        sub_routine: [0x53400593, 0x00c60563, 0x548a0596, 0x0d050563],
    };

    static SECOND_CONFIG: RomPatchConfig = RomPatchConfig {
        base_addr: 0x20000000,
        match_addr: 0x1940,
        routine_offset: 0x800,
        revision: 77,
        patch_code: [0x03a30310, 0x05a50511, 0x05a50512, 0x05a50513],
        sub_routine: [0x53400593, 0x00c60563, 0x548a0596, 0x0d030363],
    };

    fn rom_patch_hjson_str(config: &RomPatchConfig) -> String {
        format!(
            r#"{{
                   revision: {}
                   base_addr: {:#x}
                   regions: [
                      {{
                          match_addr: {:#x}
                          locked: true
                          patch_code:  {:#x?}
                          sub_routines: [
                              {{
                                   offset: {:#x}
                                   code: {:#x?}
                              }}
                          ]
                      }}
                   ]
               }}"#,
            config.revision,
            config.base_addr,
            config.match_addr,
            config.patch_code,
            config.routine_offset,
            config.sub_routine
        )
    }

    fn rom_patch_partition_hjson_str(
        first_config: &RomPatchConfig,
        second_config: &RomPatchConfig,
    ) -> String {
        format!(
            r#"{{
              patches: [
                {},
                {}
              ]
            }}"#,
            rom_patch_hjson_str(first_config),
            rom_patch_hjson_str(second_config)
        )
    }

    fn rom_test_patch<const N: usize>(config: &RomPatchConfig) -> Result<RomPatch<N>> {
        let key = EcdsaPrivateKey::load(testdata!("key_ecdsa.der"))?;
        let hjson = rom_patch_hjson_str(config);
        let patch_hjson = deser_hjson::from_str(&hjson)?;
        RomPatch::from_hjson(&patch_hjson, &key)
    }

    fn rom_test_patch_partition<const N: usize>(
        first_config: &RomPatchConfig,
        second_config: &RomPatchConfig,
    ) -> Result<RomPatchPartition<N>> {
        let key = EcdsaPrivateKey::load(testdata!("key_ecdsa.der"))?;
        let hjson = rom_patch_partition_hjson_str(first_config, second_config);
        let patch_partition_hjson = deser_hjson::from_str(&hjson)?;
        RomPatchPartition::from_hjson(&patch_partition_hjson, &key)
    }

    fn rom_patch_test_deser<const N: usize>(
        patch: &RomPatch<N>,
        config: &RomPatchConfig,
    ) -> Result<()> {
        let patch_code_size_dwords = 4;
        let sub_routine_size_dwords = 4;
        let code_size_dwords =
            (config.routine_offset / mem::size_of::<u32>()) + sub_routine_size_dwords;
        let locked_generated = patch.match_table.table[0].match_base >> PATCH_LOCKED_FIELD_SHIFT;
        let patch_code_size_dwords_generated = (patch.match_table.table[0].match_base
            >> PATCH_SIZE_FIELD_SHIFT)
            & PATCH_SIZE_FIELD_MASK;
        let match_addr_generated =
            patch.match_table.table[0].match_base & PATCH_MATCH_ADDR_FIELD_MASK;
        let remap_base_generated = patch.match_table.table[0].remap_base;

        // Check that the revision matches.
        assert_eq!(patch.header.revision, config.revision);

        // Check that the code section is correctly built.
        assert_eq!(patch.code.code.len(), code_size_dwords);
        assert_eq!(*patch.code.code.first().unwrap(), config.first_insn());
        assert_eq!(*patch.code.code.last().unwrap(), config.last_insn());

        // Check that the first patch descriptor is correct.
        assert_eq!(locked_generated, 1);
        assert_eq!(config.match_addr, match_addr_generated as usize);
        assert_eq!(config.base_addr, remap_base_generated as usize);
        assert_eq!(
            patch_code_size_dwords,
            patch_code_size_dwords_generated as usize
        );

        // Check that the second patch descriptor is all zeros.
        let second_match = patch.match_table.table[1].match_base;
        let second_remap = patch.match_table.table[1].remap_base;
        assert_eq!(second_match, 0);
        assert_eq!(second_remap, 0);

        Ok(())
    }

    fn to_vec32(bytes: &[u8]) -> Vec<u32> {
        let mut vec: Vec<u32> = Vec::with_capacity(bytes.len() / mem::size_of::<u32>());
        for chunk in bytes.chunks_exact(4) {
            let num = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            vec.push(num);
        }

        vec
    }

    fn rom_patch_test_write<const N: usize>(
        patch: &RomPatch<N>,
        config: &RomPatchConfig,
    ) -> Result<()> {
        let mut bytes: Vec<u8> = vec![];

        patch.to_writer(&mut bytes)?;
        let patch_blob = to_vec32(&bytes);

        // Check that the header is valid.
        assert_eq!(patch_blob[0], config.header());

        // Check that the first and last instructions are correctly placed.
        assert_eq!(
            patch_blob[PATCH_CODE_SECTION_OFFSET / mem::size_of::<u32>()],
            config.first_insn()
        );
        assert_eq!(
            patch_blob[((config.code_size_bytes() + PATCH_CODE_SECTION_OFFSET)
                / mem::size_of::<u32>())
                - 1],
            config.last_insn()
        );

        Ok(())
    }

    fn rom_patch_partition_test_write<const N: usize>(
        partition: &RomPatchPartition<N>,
        first_config: &RomPatchConfig,
        second_config: &RomPatchConfig,
    ) -> Result<()> {
        let first_code_size_bytes = first_config.code_size_bytes();
        let second_code_size_bytes = second_config.code_size_bytes();
        let first_patch_size_bytes = first_config.patch_size_bytes();
        let mut bytes: Vec<u8> = vec![];

        partition.to_writer(&mut bytes)?;
        let partition_blob = to_vec32(&bytes);

        // Check that the first patch header is valid.
        assert_eq!(partition_blob[0], first_config.header());

        // Check that the first and last instructions are correctly placed on the first patch.
        assert_eq!(
            partition_blob[PATCH_CODE_SECTION_OFFSET / mem::size_of::<u32>()],
            first_config.first_insn()
        );
        assert_eq!(
            partition_blob
                [((PATCH_CODE_SECTION_OFFSET + first_code_size_bytes) / mem::size_of::<u32>()) - 1],
            first_config.last_insn()
        );

        // Check that the second patch header is valid.
        assert_eq!(
            partition_blob[first_patch_size_bytes / mem::size_of::<u32>()],
            second_config.header()
        );

        // Check that the first and last instructions are correctly placed on the second patch.
        assert_eq!(
            partition_blob
                [(first_patch_size_bytes + PATCH_CODE_SECTION_OFFSET) / mem::size_of::<u32>()],
            second_config.first_insn()
        );
        assert_eq!(
            partition_blob[((first_patch_size_bytes
                + PATCH_CODE_SECTION_OFFSET
                + second_code_size_bytes)
                / mem::size_of::<u32>())
                - 1],
            second_config.last_insn()
        );

        Ok(())
    }

    #[test]
    fn test_rom_patch_match_descriptor_deser() -> Result<()> {
        let match_addr = 0x8940;
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
        let locked = match_desc.match_base >> PATCH_LOCKED_FIELD_SHIFT;
        let size = (match_desc.match_base >> PATCH_SIZE_FIELD_SHIFT) & PATCH_SIZE_FIELD_MASK;
        let remap_base = match_desc.remap_base;
        let match_addr_expected = match_desc.match_base & PATCH_MATCH_ADDR_FIELD_MASK;

        assert_eq!(remap_base, remap_addr);
        assert_eq!(match_addr_expected, match_addr);
        assert_eq!(locked, 1);
        assert_eq!(size, 4);

        Ok(())
    }

    #[test]
    fn test_rom_patch_deser() -> Result<()> {
        rom_patch_test_deser(
            &rom_test_patch::<N_MATCH_DESCRIPTORS>(&FIRST_CONFIG)?,
            &FIRST_CONFIG,
        )
    }

    #[test]
    fn test_rom_patch_write() -> Result<()> {
        rom_patch_test_write(
            &rom_test_patch::<N_MATCH_DESCRIPTORS>(&FIRST_CONFIG)?,
            &FIRST_CONFIG,
        )
    }

    #[test]
    fn test_rom_patch_partition_deser() -> Result<()> {
        let patch_partition =
            rom_test_patch_partition::<N_MATCH_DESCRIPTORS>(&FIRST_CONFIG, &SECOND_CONFIG)?;
        rom_patch_test_deser(&patch_partition.patches[0], &FIRST_CONFIG)?;
        rom_patch_test_deser(&patch_partition.patches[1], &SECOND_CONFIG)
    }

    #[test]
    fn test_rom_patch_partition_write() -> Result<()> {
        rom_patch_partition_test_write(
            &rom_test_patch_partition::<N_MATCH_DESCRIPTORS>(&FIRST_CONFIG, &SECOND_CONFIG)?,
            &FIRST_CONFIG,
            &SECOND_CONFIG,
        )
    }
}
