// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, bail};
use clap::Args;
use crc::{CRC_32_ISO_HDLC, Crc};
use std::convert::From;
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;

use crate::app::TransportWrapper;
use crate::io::fpga_backdoor::{
    Backdoor, BackdoorParams, BackdoorTarget, BackdoorTargetInfo, enter_backdoor_loader,
};
use crate::io::jtag::JtagParams;
use crate::util::vmem::{Section, Vmem, Word};

// Reset the SoC and enter the backdoor loader, initializing a connection via JTAG.
pub fn enter_backdoor(transport: &TransportWrapper, jtag_params: &JtagParams) -> Result<Backdoor> {
    enter_backdoor_loader(transport)?;
    let backdoor_params = BackdoorParams {
        jtag: jtag_params.clone(),
    };
    backdoor_params.create(transport)?.connect(true)
}

// Normalize a word to a given number of bits.
fn normalize_word(word: &mut Word, bits_per_word: usize) {
    let bytes_per_word = bits_per_word.div_ceil(8);
    if word.bytes.len() > bytes_per_word {
        let start = word.bytes.len() - bytes_per_word;
        word.bytes.drain(..start);
    } else if word.bytes.len() < bytes_per_word {
        let mut padded = vec![0u8; bytes_per_word - word.bytes.len()];
        padded.append(&mut word.bytes);
        word.bytes = padded;
    }

    let extra_bits = bits_per_word % 8;
    if extra_bits > 0 {
        word.bytes[0] &= 0xFF >> (8 - extra_bits);
    }
}

// Check that words read from target memory match input words.
pub fn verify_readback(
    input: &mut [Word],
    readback: &mut [Word],
    bits_per_word: usize,
    mut offset: u32,
) -> Result<()> {
    for (write_word, read_word) in readback.iter_mut().zip(input) {
        normalize_word(write_word, bits_per_word);
        normalize_word(read_word, bits_per_word);
        if write_word != read_word {
            bail!(
                "Read verification at word {} failed. Expected: {}, Got: {}",
                offset,
                hex::encode(write_word.bytes.clone()),
                hex::encode(read_word.bytes.clone()),
            );
        }

        offset += 1;
    }

    Ok(())
}

pub fn write_to_target(
    target: &mut BackdoorTarget,
    target_id: &str,
    data: Vec<Section>,
    verify: bool,
) -> Result<()> {
    // Perform the write(s)
    log::info!("Writing to the {}...", target_id);
    for mut section in data {
        log::debug!(
            "Writing section of size {} to word {} of target {}",
            section.data.len(),
            section.addr,
            target_id
        );

        // Special case - if we're just trying to clear the entire target memory,
        // instead use the fast clearing operation.
        let first_word = &section.data.first().clone();
        if section.addr == 0
            && section.data.len() == target.info.depth as usize
            && section.data.iter().all(|w| w == first_word.unwrap())
        {
            log::debug!(
                "Clearing target {} with word {}",
                target_id,
                hex::encode(first_word.unwrap().bytes.clone())
            );
            target.clear(first_word.unwrap(), verify)?;
        } else {
            target.write(section.addr, &section.data, false, verify)?;
        }

        // If requested, read back the data and verify against written contents
        if verify {
            let mut readback = target.read(section.addr, section.data.len() as u32, false)?;
            verify_readback(
                &mut section.data,
                &mut readback,
                target.info.width as usize,
                section.addr,
            )?;
        }
    }

    Ok(())
}

#[derive(Debug, Clone)]
pub struct TargetWrite {
    pub target: String,
    pub path: PathBuf,
    pub offset: Option<u32>,
}

impl FromStr for TargetWrite {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (target_path, offset) = s
            .split_once('@')
            .map(|(x, y)| (x, y.parse::<u32>().ok()))
            .unwrap_or((s, None));

        let (target, path) = target_path
            .split_once('=')
            .context("expected input like TARGET=FILE[@OFFSET], but no '=' was seen")?;
        if target.is_empty() {
            bail!("target name cannot be empty");
        }
        if path.is_empty() {
            bail!("file path cannot be empty");
        }

        Ok(TargetWrite {
            target: target.to_string(),
            path: PathBuf::from(path),
            offset,
        })
    }
}

impl TargetWrite {
    pub fn load_data(&self) -> Result<Vec<Section>> {
        log::info!("Loading VMEM file: {}", self.path.display());
        let vmem_content = fs::read_to_string(&self.path)?;
        let mut vmem = Vmem::from_str(&vmem_content, None)?;
        vmem.merge_sections(None);
        let mut sections: Vec<Section> = vmem.sections().cloned().collect();

        // If an offset is given, all sections must be offset by that amount.
        if let Some(offset) = self.offset {
            for section in &mut sections {
                section.addr += offset;
            }
        }

        Ok(sections)
    }

    /// CRC32 (ISO-HDLC, the same variant used elsewhere in this crate, e.g.
    /// `util::usr_access`/`test_utils::load_sram_program`) of the raw VMEM file content, used
    /// to decide whether this exact content is already preloaded on the target (see
    /// `backdoor_write` and the target's `HASH_LAST_LOADED` register).
    fn file_hash(&self) -> Result<u32> {
        let bytes = fs::read(&self.path)
            .with_context(|| format!("failed to read VMEM file: {}", self.path.display()))?;
        Ok(Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(&bytes))
    }

    /// Write this file to `backdoor`'s target.
    ///
    /// If `check_hash` is set, the preload is skipped entirely when the target's
    /// `HASH_LAST_LOADED` register already reports a hash matching this file's content --
    /// `HASH_LAST_LOADED` survives the backdoor loader's own resets (see
    /// `Backdoor::read_target_hash`), so this holds across consecutive tool invocations as
    /// long as the FPGA itself isn't power-cycled/reflashed. When `check_hash` is clear, the
    /// hash register is left untouched and the preload always happens unconditionally, as
    /// before this check existed.
    pub fn backdoor_write(
        &self,
        backdoor: &mut Backdoor,
        verify: bool,
        check_hash: bool,
    ) -> Result<()> {
        let mut target = backdoor
            .target_by_id_str(&self.target)?
            .context(format!("FPGA target '{}' not found", &self.target))?;

        let new_hash = if check_hash {
            let new_hash = self.file_hash()?;
            let old_hash = target.read_hash()?;
            if old_hash == new_hash {
                log::info!(
                    "Skipping preload of target {}: content hash unchanged (0x{new_hash:08x})",
                    self.target,
                );
                return Ok(());
            }
            log::info!(
                "Preloading target {}: content hash changed (old=0x{old_hash:08x}, new=0x{new_hash:08x})",
                self.target,
            );
            Some(new_hash)
        } else {
            None
        };

        let data = self.load_data()?;
        write_to_target(&mut target, &self.target, data, verify)?;
        if let Some(new_hash) = new_hash {
            target.write_hash(new_hash)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct TargetClear {
    pub target: String,
    pub num_words: Option<u32>,
    pub offset: Option<u32>,
}

impl FromStr for TargetClear {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (target_words, offset) = s
            .split_once('@')
            .map(|(x, y)| (x, y.parse::<u32>().ok()))
            .unwrap_or((s, None));

        let (target, num_words) = target_words
            .split_once('=')
            .context("expected input like TARGET=NUM_WORDS[@OFFSET], but no '=' was seen")?;
        if target.is_empty() {
            bail!("target name cannot be empty");
        }
        if num_words.is_empty() {
            bail!("num_words cannot be empty");
        }
        let num_words = if num_words.to_lowercase() == "all" {
            None
        } else {
            Some(num_words.parse::<u32>()?)
        };

        Ok(TargetClear {
            target: target.to_string(),
            num_words,
            offset,
        })
    }
}

impl TargetClear {
    pub fn as_sections(&self, target_info: &BackdoorTargetInfo) -> Vec<Section> {
        let num_bytes = target_info.width.div_ceil(8) as usize;
        let remaining_words = target_info.depth - self.offset.unwrap_or(0);
        let num_words = self.num_words.unwrap_or(remaining_words);
        let data = vec![Word::new(vec![0x00; num_bytes]); num_words as usize];
        vec![Section {
            addr: self.offset.unwrap_or(0),
            data,
        }]
    }

    pub fn backdoor_write(&self, backdoor: &mut Backdoor, verify: bool) -> Result<()> {
        let mut target = backdoor
            .target_by_id_str(&self.target)?
            .context(format!("FPGA target '{}' not found", &self.target))?;

        let data = self.as_sections(&target.info);
        write_to_target(&mut target, &self.target, data, verify)
    }
}

// Write FPGA memories after loading the bitstream
#[derive(Debug, Args)]
pub struct LoadMemories {
    /// Memories to be cleared / zeroed. All clears apply before writes.
    #[arg(long = "clear-memory", value_name = "TARGET=NUM_WORDS[@OFFSET]")]
    pub target_clears: Vec<TargetClear>,

    /// Memories to be written, mapping VMEM files to FPGA target memories.
    #[arg(long = "load-memory", value_name = "TARGET=FILE[@OFFSET]")]
    pub target_writes: Vec<TargetWrite>,

    /// Targets (matching a name given to `--load-memory`) for which the memory file's hash is
    /// checked against the target's HASH_LAST_LOADED register before writing, skipping the
    /// preload if it's unchanged since the last time this target was written. Only targets
    /// named here are checked; any other `--load-memory` target is always preloaded
    /// unconditionally.
    #[arg(long = "check-memory-hash", value_name = "TARGET")]
    pub check_memory_hash: Vec<String>,
}

impl LoadMemories {
    pub fn init(&self, transport: &TransportWrapper, jtag_params: &JtagParams) -> Result<()> {
        if self.target_clears.is_empty() && self.target_writes.is_empty() {
            return Ok(());
        }

        let mut backdoor = enter_backdoor(transport, jtag_params)?;
        self.target_clears
            .iter()
            .try_for_each(|t| t.backdoor_write(&mut backdoor, false))?;
        self.target_writes.iter().try_for_each(|t| {
            let check_hash = self.check_memory_hash.contains(&t.target);
            t.backdoor_write(&mut backdoor, false, check_hash)
        })?;
        backdoor.set_done()?;

        Ok(())
    }
}

// Unit tests for `TargetWrite::file_hash`, the VMEM-file content hashing used by the
// `--check-memory-hash` skip-preload feature. These only exercise the pure hashing logic
// against local temp files, so they don't require real hardware/JTAG.
#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Seek, SeekFrom, Write};

    #[test]
    fn file_hash_matches_known_crc32_iso_hdlc_check_value() {
        // "123456789" is the standard CRC-32/ISO-HDLC ("check") test vector; its checksum is
        // published as 0xcbf43926, independent of this crate's implementation.
        let mut file = tempfile::NamedTempFile::new().unwrap();
        file.write_all(b"123456789").unwrap();

        let target_write = TargetWrite {
            target: "TEST".to_string(),
            path: file.path().to_path_buf(),
            offset: None,
        };
        assert_eq!(target_write.file_hash().unwrap(), 0xcbf43926);
    }

    #[test]
    fn file_hash_changes_with_content() {
        let mut file = tempfile::NamedTempFile::new().unwrap();
        file.write_all(b"hello").unwrap();
        let target_write = TargetWrite {
            target: "TEST".to_string(),
            path: file.path().to_path_buf(),
            offset: None,
        };
        let hash_a = target_write.file_hash().unwrap();

        file.as_file_mut().set_len(0).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        file.write_all(b"world").unwrap();
        let hash_b = target_write.file_hash().unwrap();

        assert_ne!(hash_a, hash_b);
    }
}
