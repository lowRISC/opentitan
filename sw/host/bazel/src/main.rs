// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::fs::{File, OpenOptions};
use std::io::BufReader;
use std::path::{Path, PathBuf};

use exec_log_lib::bazel_exec_log;
use exec_log_lib::exec_log::ExecLog;

use spawn_proto::protos::SpawnExec;

/// File format of the log file.
#[derive(Copy, Clone, Debug, Eq, PartialEq,ValueEnum)]
#[value(rename_all = "kebab-case")]
enum Format {
    /// Bazel binary execution log (protobuf).
    BazelBin,
    /// Opentitan json format.
    OtJson,
}

/// Operation to perform.
#[derive(Debug, Subcommand)]
#[command(rename_all = "kebab-case")]
enum Operation {
    /// Convert between formats.
    Convert(ConvertCommand),
    /// Print the log.
    Print(PrintCommand),
}

/// Conversion command.
#[derive(Debug, Args)]
struct ConvertCommand {
    /// Input format. If not set, will guess format based on extension.
    #[arg(long)]
    in_format: Option<Format>,
    /// Output format. If not set, will guess format based on extension.
    #[arg(long)]
    out_format: Option<Format>,
    /// Input file.
    input: PathBuf,
    /// Output file.
    output: PathBuf,
}

/// Printing command.
#[derive(Debug, Args)]
struct PrintCommand {
    /// Input format. If not set, will guess format based on extension.
    #[arg(long)]
    format: Option<Format>,
    /// Input file.
    input: PathBuf,
}

#[derive(Debug, Parser)]
#[command(
    name = "exec_log",
    about = "A tool for working with bazel execution logs"
)]
struct Opts {
    #[command(subcommand)]
    operation: Operation,
}

fn guess_format(fmt: &Option<Format>, path: &Path) -> Result<Format> {
    if let Some(fmt) = fmt {
        return Ok(*fmt)
    }
    let ext = path.extension();
    let Some(ext) = ext else {
        bail!("Cannot guess log format since the file has no extension");
    };
    let Some(ext) = ext.to_str() else {
        bail!("Cannot convert file extension to UTF-8 so cannot guess log format");
    };
    match ext {
        "log" => Ok(Format::BazelBin),
        "json" => Ok(Format::OtJson),
        _ => bail!("unknown extension {ext}, cannot guess log format"),
    }
}

fn convert(conv: &ConvertCommand) -> Result<()> {
    let in_fmt = guess_format(&conv.in_format, &conv.input)?;
    let out_fmt = guess_format(&conv.out_format, &conv.output)?;

    ensure!(in_fmt == Format::BazelBin, "only supports bazel binary log as input");
    ensure!(out_fmt == Format::OtJson, "only supports opentitan json log as output");

    let file = File::open(&conv.input)?;
    let mut reader = BufReader::with_capacity(10_000_000, file);
    let mut buf = Vec::<u8>::new();

    let elapsed = std::time::Instant::now();
    let mut msg = SpawnExec::default();
    let mut exec_log = ExecLog::new();

    loop {
        if !bazel_exec_log::read_spawn_exec(&mut reader, &mut msg, &mut buf)? {
            break;
        };
        exec_log.add_bazel_entry(&msg);
    }
    println!("parsing took {}ms", elapsed.elapsed().as_millis());

    println!("{exec_log:#?}");

    let elapsed = std::time::Instant::now();
    let file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&conv.output)?;
    serde_json::to_writer(&file, &exec_log)?;
    println!("serialization took {}ms", elapsed.elapsed().as_millis());

    Ok(())
}

fn print_bazel(print: &PrintCommand) -> Result<()> {
    let file = File::open(&print.input)?;
    let mut reader = BufReader::with_capacity(10_000_000, file);
    let mut buf = Vec::<u8>::new();

    let mut msg = SpawnExec::default();

    loop {
        if !bazel_exec_log::read_spawn_exec(&mut reader, &mut msg, &mut buf)? {
            break;
        };
        // println!("{msg:#?}");
        println!("{:#?}", msg.environment_variables);
    }
    Ok(())
}

fn print_ot_json(print: &PrintCommand) -> Result<()> {
    let file = File::open(&print.input)?;
    let reader = BufReader::new(file);
    let exec_log: ExecLog = serde_json::from_reader(reader)?;

    println!("{exec_log:#?}");
    Ok(())
}

fn print_log(print: &PrintCommand) -> Result<()> {
    let fmt = guess_format(&print.format, &print.input)?;

    match fmt {
        Format::BazelBin => print_bazel(print),
        Format::OtJson => print_ot_json(print),
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();

    match opts.operation {
        Operation::Convert(conv) => convert(&conv),
        Operation::Print(print) => print_log(&print),
    }
}
