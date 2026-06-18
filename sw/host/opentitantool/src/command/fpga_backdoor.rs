// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use std::any::Any;
use std::convert::From;
use std::fs;
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::io::fpga_backdoor::{BackdoorParams, BackdoorTargetInfo, enter_backdoor_loader};
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
