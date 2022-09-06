// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::otp::lc_state::LcSecded;
use crate::util::present::Present;

use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt::Write;

use anyhow::{anyhow, bail, ensure, Result};

use zerocopy::AsBytes;

enum ItemType {
    Bytes(Vec<u8>),
    Unvalued(usize),
}

/// The hex representation of an OTP item.
pub struct VmemItem {
    value: ItemType,
    offset: usize,
    name: String,
}

impl VmemItem {
    pub fn new(bytes: Vec<u8>, offset: usize, name: String) -> VmemItem {
        VmemItem {
            value: ItemType::Bytes(bytes),
            offset,
            name,
        }
    }

    pub fn new_unvalued(size: usize, offset: usize, name: String) -> VmemItem {
        VmemItem {
            value: ItemType::Unvalued(size),
            offset,
            name,
        }
    }

    pub fn size(&self) -> usize {
        match &self.value {
            ItemType::Bytes(b) => b.len(),
            ItemType::Unvalued(size) => *size,
        }
    }
}

pub type DigestIV = u64;
pub type DigestCnst = u128;

/// Digest information for an OTP partition.
#[derive(PartialEq)]
pub enum DigestType {
    Unlocked,
    Software,
    Hardware(DigestIV, DigestCnst),
}

/// The hex representation of an OTP partition.
pub struct VmemPartition {
    /// Items associated with this partition.
    items: Vec<VmemItem>,
    /// The name of this partition.
    /// Used in annotations.
    name: String,
    /// The type of digest used for this partition.
    /// For software digests, the value of the digest is provided and appended to the list of
    /// items. For hardware digests, we must compute the digest value and append to the list of
    /// items.
    digest_type: DigestType,
    /// Partition size.
    size: usize,
    /// The key name for this partition.
    /// If specified, the serializer will attempt to scramble this partition using the key named in
    /// this field.
    key_name: Option<String>,
}

impl VmemPartition {
    pub fn new(
        name: String,
        size: usize,
        digest_type: DigestType,
        key_name: Option<String>,
    ) -> VmemPartition {
        VmemPartition {
            items: Vec::new(),
            name,
            digest_type,
            size,
            key_name,
        }
    }

    /// Set the size of the partition.
    ///
    /// For partitions that don't specify their size, this is used to set the size of the partition
    /// including the digest.
    pub fn set_size(&mut self, size: usize) {
        self.size = size;
    }

    /// Add an item to this partition.
    pub fn push_item(&mut self, item: VmemItem) {
        self.items.push(item);
    }

    /// Produces a tuple containing OTP HEX lines with annotations.
    fn write_to_buffer(&self, keys: &HashMap<String, Vec<u8>>) -> Result<(Vec<u8>, Vec<String>)> {
        if self.size % 8 != 0 {
            bail!("Partition {} must be 64-bit alligned", self.name);
        }

        let mut defined = vec![false; self.size];
        let mut annotations: Vec<String> = vec!["unallocated".to_owned(); self.size];

        let mut data_bytes: Vec<u8> = vec![0; self.size];

        for item in &self.items {
            let end = item.offset + item.size();
            annotations[item.offset..end].fill(format!("{}: {}", self.name, item.name).to_string());
            let defined = &mut defined[item.offset..end];
            if let Some(collision) = defined.iter().position(|defined| *defined) {
                bail!(
                    "Unexpected item collision with item {} at 0x{:x}",
                    item.name,
                    collision
                );
            }
            defined.fill(true);
            if let ItemType::Bytes(bytes) = &item.value {
                data_bytes[item.offset..end].copy_from_slice(bytes);
            }
        }

        let mut data_blocks = Vec::<u64>::new();
        let mut data_blocks_defined = Vec::<bool>::new();
        for (k, chunk) in data_bytes.chunks(8).enumerate() {
            data_blocks.push(u64::from_le_bytes(chunk.try_into().unwrap()));
            let byte_offset = k * 8;
            data_blocks_defined.push(
                defined[byte_offset..byte_offset + 8]
                    .iter()
                    .fold(false, |a, &b| a || b),
            );
        }

        if let Some(key_name) = &self.key_name {
            let key = keys
                .get(key_name)
                .ok_or_else(|| anyhow!("Key not found {}", key_name))?;

            let cipher = Present::try_new(key.clone())?;

            for i in 0..data_blocks.len() {
                if data_blocks_defined[i] {
                    data_blocks[i] = cipher.encrypt_block(data_blocks[i]);
                }
            }
        }

        if let DigestType::Hardware(iv, fin_const) = self.digest_type {
            ensure!(
                matches!(data_blocks.last(), None | Some(0)),
                "Digest of partition {} cannot be overridden manually",
                self.name
            );
            let last = data_blocks.len() - 1;
            data_blocks[last] = present_digest_64(&data_blocks[0..last], iv, fin_const);
        }

        let data = data_blocks.as_bytes().to_vec();

        if data.len() != self.size {
            Err(anyhow!("Partition {} size mismatch", self.name))
        } else {
            Ok((data, annotations))
        }
    }
}

pub struct VmemImage {
    partitions: Vec<VmemPartition>,
    width: usize,
    depth: usize,
}

impl VmemImage {
    pub fn new(partitions: Vec<VmemPartition>, width: usize, depth: usize) -> VmemImage {
        VmemImage {
            partitions,
            width,
            depth,
        }
    }
    pub fn generate(
        &self,
        keys: HashMap<String, Vec<u8>>,
        secded: &LcSecded,
    ) -> Result<Vec<String>> {
        let mut data: Vec<u8> = vec![0; self.width * self.depth];
        let mut annotations: Vec<String> = vec![Default::default(); data.len()];
        let mut offset = 0;
        for partition in &self.partitions {
            let (part_data, part_annotation) = partition.write_to_buffer(&keys)?;
            let end = offset + partition.size;
            if end > data.len() {
                bail!(
                    "Partition {} out of bounds, ends at 0x{:x}",
                    partition.name,
                    end
                );
            }
            data[offset..end].clone_from_slice(&part_data);
            annotations[offset..end].clone_from_slice(&part_annotation);
            offset += partition.size;
        }

        let width_ecc = self.width + secded.ecc_byte_len();
        let num_words = data.len() / self.width;

        let mut output = vec![format!(
            "// OTP memory hexfile with {} x {}bit layout",
            self.depth,
            width_ecc * 8
        )];

        for i in 0..num_words {
            let mut word = Vec::<u8>::new();
            let mut word_annotation = Vec::<String>::new();
            for j in 0..self.width {
                let idx = i * self.width + j;
                word.push(data[idx]);
                if !word_annotation.contains(&annotations[idx]) {
                    word_annotation.push(annotations[idx].clone());
                }
            }
            let word_with_ecc = secded.ecc_encode(word)?;
            let mut word_str = String::new();
            for byte in word_with_ecc.iter().rev() {
                write!(word_str, "{:02x}", byte)?;
            }
            output.push(format!(
                "{} // {:06x}: {}",
                word_str,
                i * self.width,
                word_annotation.join(", ")
            ));
        }

        Ok(output)
    }
}

fn present_digest_64(message: &[u64], iv: DigestIV, fin_const: DigestCnst) -> u64 {
    let mut state = iv;
    for i in (0..message.len() + 2).step_by(2) {
        let b128: [u8; 16] = if i + 1 < message.len() {
            (message[i] as u128) << 64 | message[i + 1] as u128
        } else if i < message.len() {
            (message[i] as u128) << 64 | message[i] as u128
        } else {
            fin_const
        }
        .as_bytes()
        .try_into()
        .unwrap();

        let cipher = Present::new_128(&b128);
        state ^= cipher.encrypt_block(state);
    }

    state
}
