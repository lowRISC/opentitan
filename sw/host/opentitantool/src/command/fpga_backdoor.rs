// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, bail};
use clap::{Args, Subcommand};
use std::any::Any;
use std::convert::From;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::str::FromStr;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::io::fpga_backdoor::{
    Backdoor, BackdoorParams, BackdoorTargetInfo, enter_backdoor_loader,
};
use opentitanlib::util::parse_int::ParseInt;
use opentitanlib::util::vmem::{Section, Vmem, Word};

/// Commands for interacting with the backdoor FPGA loader.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum InternalBackdoorCommand {
    /// Enter the backdoor loader - this *requires* resetting the device.
    Enter(BackdoorEnter),
    /// Exit the backdoor loader, finishing and de-asserting reset. Irreversible until next reset.
    Exit(BackdoorExit),
    /// Display information about the available backdoor targets
    Info(BackdoorInfo),
    /// Read words from a target memory via the backdoor.
    Read(BackdoorRead),
    /// Write words to a target memory via the backdoor.
    Write(BackdoorWrite),
    /// Verify that the contents of some target memory matches some given data.
    Verify(BackdoorVerify),
    /// A command that combines entering, writing several files to different targets, and starting.
    Batch(BackdoorBatch),
}

#[derive(Debug, Args)]
pub struct BackdoorEnter {}

impl CommandDispatch for BackdoorEnter {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        enter_backdoor_loader(transport)?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorExit {}

impl CommandDispatch for BackdoorExit {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let backdoor = backdoor.connect(false)?;
        backdoor.set_done()?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorInfo {
    /// Optional target to query. If not specified, returns info for all targets.
    pub target: Option<String>,
}

impl CommandDispatch for BackdoorInfo {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let mut backdoor = backdoor.connect(true)?;

        let info: Box<dyn erased_serde::Serialize> = match &self.target {
            Some(id_str) => {
                let target = backdoor
                    .target_by_id_str(id_str)?
                    .context(format!("FPGA target '{id_str}' not found"))?;
                Box::new(target.info)
            }
            None => Box::new(backdoor.targets().to_vec()),
        };

        Ok(Some(info))
    }
}

/// Output formats for data that is read from the backdoor loader.
#[derive(clap::ValueEnum, Clone, Copy, Debug)]
pub enum OutputFormat {
    Hex,
    Raw,
    Vmem,
}

#[derive(Debug, Args)]
pub struct BackdoorRead {
    /// Target to read from.
    pub target: String,

    /// First word address / index to read from.
    #[arg(long, value_parser = <u32 as ParseInt>::from_str, default_value = "0")]
    pub start: u32,

    /// The number of words to read. If not given, reads the entire memory.
    #[arg(long, alias = "words", value_parser = <u32 as ParseInt>::from_str)]
    pub length: Option<u32>,

    /// Optional path to write the output to. If not given, outputs directly to stdout.
    #[arg(short, long)]
    pub output: Option<PathBuf>,

    /// The data format to use when outputting words that are read.
    #[arg(long, default_value = "hex")]
    pub format: OutputFormat,

    /// If outputting as a Vmem, omit extraneous element indexes for contiguous words
    #[arg(long)]
    pub group_vmem_words: bool,
}

fn output_read_contents(
    output: Option<&PathBuf>,
    start: u32,
    words: Vec<Word>,
    target_info: &BackdoorTargetInfo,
    format: OutputFormat,
    group_vmem_words: bool,
) -> Result<()> {
    let mut out: Box<dyn Write> = if let Some(out_path) = &output {
        Box::new(fs::File::create(out_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    match format {
        OutputFormat::Hex => {
            let hex = words
                .into_iter()
                .map(|w| hex::encode(w.bytes))
                .collect::<Vec<_>>()
                .join(" ");
            writeln!(out, "{}", hex)?;
        }
        OutputFormat::Raw => {
            for word in words {
                out.write_all(&word.bytes)?;
            }
        }
        OutputFormat::Vmem => {
            let num_bytes = target_info.width.div_ceil(8);
            writeln!(
                out,
                "// {} memory file with {} x {} bit layout ({} x {} bytes)",
                target_info.id_str(),
                target_info.width,
                target_info.depth,
                num_bytes,
                target_info.depth
            )?;
            let vmem = Vmem::new(vec![Section {
                addr: start,
                data: words,
            }]);
            writeln!(out, "{}", vmem.dump(None, !group_vmem_words))?;
        }
    }

    Ok(())
}

impl CommandDispatch for BackdoorRead {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();

        // Connect to the backdoor and try and find the requested target.
        let backdoor = context.params.create(transport)?;
        let mut backdoor = backdoor.connect(true)?;
        let mut target = backdoor
            .target_by_id_str(&self.target)?
            .context(format!("FPGA target '{}' not found", self.target))?;
        let words = self.length.unwrap_or(target.info.depth - self.start);

        // Read and output the requested data
        log::info!(
            "Reading {} words at offset {} from target {}...",
            words,
            self.start,
            self.target
        );
        let words = target.read(self.start, words, true)?;
        output_read_contents(
            self.output.as_ref(),
            self.start,
            words,
            &target.info,
            self.format,
            self.group_vmem_words,
        )?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorWrite {
    /// Target to write to.
    pub target: String,

    /// First word address / index to write to.
    #[arg(long, value_parser = <u32 as ParseInt>::from_str)]
    pub offset: Option<u32>,

    /// Read back and verify the written data (may take noticeably longer).
    #[arg(long)]
    pub verify: bool,

    /// The input source to write
    #[command(subcommand)]
    pub input: WriteInput,
}

#[derive(Debug, Subcommand)]
pub enum WriteInput {
    /// Write/verify words given as a whitespace-separated hex string
    Hex(HexInput),
    /// Write/verify words that are some repeated clear pattern (e.g. all 0s, 0xA5 repeated)
    Clear(ClearInput),
    /// Write/verify words loaded from a Verilog VMEM file
    Vmem(VmemInput),
}

#[derive(Args, Debug)]
pub struct HexInput {
    /// Input hexadecimal words, with whitespace separating each word
    #[arg(required = true, num_args = 1..)]
    pub data: Vec<String>,
}

#[derive(Args, Debug)]
pub struct ClearInput {
    /// The number of cleared words. If unspecified, the remainder of the target is cleared.
    #[arg(value_parser = <u32 as ParseInt>::from_str)]
    pub words: Option<u32>,

    /// The pattern (byte) that is repeated.
    #[arg(long, value_parser = <u8 as ParseInt>::from_str, default_value = "0x00")]
    pub pattern: u8,
}

#[derive(Args, Debug)]
pub struct VmemInput {
    /// Path to the Verilog VMEM file
    pub path: PathBuf,
}

impl WriteInput {
    fn load_hex_words(hex: &HexInput) -> Result<Vec<Section>> {
        let words = hex
            .data
            .join(" ")
            .split_whitespace()
            .map(|word| {
                let normalized = word
                    .strip_prefix("0x")
                    .or_else(|| word.strip_prefix("0X"))
                    .unwrap_or(word);
                let normalized = if normalized.len() % 2 != 0 {
                    format!("0{}", normalized)
                } else {
                    String::from(normalized)
                };

                Ok(Word::new(hex::decode(normalized)?))
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(vec![Section {
            addr: 0,
            data: words,
        }])
    }

    fn load_input(
        input: &WriteInput,
        target_info: &BackdoorTargetInfo,
        offset: Option<u32>,
    ) -> Result<Vec<Section>> {
        let mut sections: Vec<Section> = match input {
            WriteInput::Hex(hex) => WriteInput::load_hex_words(hex)?,
            WriteInput::Clear(clear) => {
                let num_bytes = target_info.width.div_ceil(8) as usize;
                let remaining_words = target_info.depth - offset.unwrap_or(0);
                let num_words = clear.words.unwrap_or(remaining_words);
                let data = vec![Word::new(vec![clear.pattern; num_bytes]); num_words as usize];
                vec![Section { addr: 0, data }]
            }
            WriteInput::Vmem(vmem) => {
                log::info!("Loading VMEM file: {}", vmem.path.display());
                let vmem_content = fs::read_to_string(&vmem.path)?;
                let mut vmem = Vmem::from_str(&vmem_content, None)?;
                vmem.merge_sections(None);
                vmem.sections().cloned().collect()
            }
        };

        // If an offset is given, all sections must be offset by that amount.
        if let Some(offset) = offset {
            for section in &mut sections {
                section.addr += offset;
            }
        }

        Ok(sections)
    }
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
fn verify_readback(
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

fn write_to_target(
    backdoor: &mut Backdoor,
    target_id: &str,
    input: &WriteInput,
    offset: Option<u32>,
    verify: bool,
) -> Result<()> {
    // Try and find the requested target.
    let mut target = backdoor
        .target_by_id_str(target_id)?
        .context(format!("FPGA target '{}' not found", target_id))?;

    // Parse the input, which will depend on the given input type.
    let sections: Vec<Section> = WriteInput::load_input(input, &target.info, offset)?;

    // Perform the write(s)
    log::info!("Writing to the {}...", target_id);
    for mut section in sections {
        log::debug!(
            "Writing section of size {} to word {} of target {}",
            section.data.len(),
            section.addr,
            target_id
        );
        target.write(section.addr, &section.data, false, verify)?;

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

impl CommandDispatch for BackdoorWrite {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let mut backdoor = backdoor.connect(true)?;
        write_to_target(
            &mut backdoor,
            &self.target,
            &self.input,
            self.offset,
            self.verify,
        )?;

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorVerify {
    /// Target to verify the contents of.
    pub target: String,

    /// First word address / index to read from.
    #[arg(long, value_parser = <u32 as ParseInt>::from_str)]
    pub offset: Option<u32>,

    /// The input source to verify against.
    #[command(subcommand)]
    pub input: WriteInput,
}

impl CommandDispatch for BackdoorVerify {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();

        // Connect to the backdoor and try and find the requested target.
        let backdoor = context.params.create(transport)?;
        let mut backdoor = backdoor.connect(true)?;
        let mut target = backdoor
            .target_by_id_str(&self.target)?
            .context(format!("FPGA target '{}' not found", self.target))?;

        // Parse the input, which will depend on the given input type.
        let sections: Vec<Section> =
            WriteInput::load_input(&self.input, &target.info, self.offset)?;

        // Read the data and check it matches our input.
        log::info!("Verifying the {}...", self.target);
        for mut section in sections {
            log::debug!(
                "Verifying section of size {} at word {} of target {}",
                section.data.len(),
                section.addr,
                self.target
            );
            let mut readback = target.read(section.addr, section.data.len() as u32, false)?;
            verify_readback(
                &mut section.data,
                &mut readback,
                target.info.width as usize,
                section.addr,
            )?;
        }

        Ok(None)
    }
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

#[derive(Debug, Args)]
pub struct BackdoorBatch {
    /// Write operations to be batched, mapping VMEM files to FPGA targets.
    #[arg(long = "write", required = true, value_name = "TARGET=FILE[@OFFSET]")]
    pub targets: Vec<TargetWrite>,

    /// After completing all writes, enter "mission mode" & start the chip.
    #[arg(long)]
    pub start: bool,

    /// Read back and verify the written data (may take noticeably longer).
    #[arg(long)]
    pub verify: bool,
}

impl CommandDispatch for BackdoorBatch {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        let context = context.downcast_ref::<BackdoorCommand>().unwrap();
        let backdoor = context.params.create(transport)?;
        let mut backdoor = backdoor.connect(true)?;

        for write_op in &self.targets {
            let input = WriteInput::Vmem(VmemInput {
                path: write_op.path.clone(),
            });
            write_to_target(
                &mut backdoor,
                &write_op.target,
                &input,
                write_op.offset,
                self.verify,
            )?;
        }

        if self.start {
            backdoor.set_done()?;
        }

        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct BackdoorCommand {
    #[command(flatten)]
    params: BackdoorParams,

    #[command(subcommand)]
    command: InternalBackdoorCommand,
}

impl CommandDispatch for BackdoorCommand {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        self.command.run(self, transport)
    }
}
