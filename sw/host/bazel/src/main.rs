// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::BufReader;
use std::path::{Path, PathBuf};

use exec_log_lib::bazel_exec_log;
use exec_log_lib::exec_log::ExecLog;

use spawn_proto::protos::SpawnExec;

/// File format of the log file.
#[derive(Copy, Clone, Debug, Eq, PartialEq, ValueEnum)]
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
    /// Compare two logs.
    Compare(CompareCommand),
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

/// Compare command.
#[derive(Debug, Args)]
struct CompareCommand {
    /// Input A format. If not set, will guess format based on extension.
    #[arg(long)]
    format_a: Option<Format>,
    /// Input file A.
    input_a: PathBuf,
    /// Input B format. If not set, will guess format based on extension.
    #[arg(long)]
    format_b: Option<Format>,
    /// Input file B.
    input_b: PathBuf,
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
        return Ok(*fmt);
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

    ensure!(
        in_fmt == Format::BazelBin,
        "only supports bazel binary log as input"
    );
    ensure!(
        out_fmt == Format::OtJson,
        "only supports opentitan json log as output"
    );

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
        println!("{msg:#?}");
    }
    Ok(())
}

fn read_ot_log(path: &Path) -> Result<ExecLog> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    Ok(serde_json::from_reader(reader)?)
}

fn print_ot_json(print: &PrintCommand) -> Result<()> {
    let exec_log = read_ot_log(&print.input)?;

    for entry in exec_log.iter_entries() {
        println!("{entry:#?}");
    }

    Ok(())
}

fn print_log(print: &PrintCommand) -> Result<()> {
    let fmt = guess_format(&print.format, &print.input)?;

    match fmt {
        Format::BazelBin => print_bazel(print),
        Format::OtJson => print_ot_json(print),
    }
}

fn compare_logs(cmp: &CompareCommand) -> Result<()> {
    let fmt_a = guess_format(&cmp.format_a, &cmp.input_a)?;
    let fmt_b = guess_format(&cmp.format_b, &cmp.input_b)?;

    ensure!(
        fmt_a == Format::OtJson && fmt_b == Format::OtJson,
        "the compare command only supports the ot-json format"
    );

    let input_a = read_ot_log(&cmp.input_a)?;
    let input_b = read_ot_log(&cmp.input_b)?;
    // Map from file name to digest string.
    let mut file_digest_map = HashMap::<&str, &str>::new();
    let mut diff_files = HashSet::<&str>::new();
    // Insert all files for A.
    for file_a in input_a.iter_files() {
        // Ignore files with no digest.
        let Some(digest) = file_a.digest() else {
            continue;
        };
        file_digest_map.insert(file_a.path(), digest.hash());
    }
    // Compare with all files from B.
    for file_b in input_b.iter_files() {
        // Ignore files with no digest.
        let Some(digest_b) = file_b.digest() else {
            continue;
        };
        match file_digest_map.get(file_b.path()) {
            None => println!("File '{}' exists in A but not in B", file_b.path()),
            Some(digest_a) if digest_a != &digest_b.hash() => {
                println!(
                    "File '{}' has different hash ({} in A, {} in B)",
                    file_b.path(),
                    digest_a,
                    digest_b.hash()
                );
                diff_files.insert(file_b.path());
            }
            _ => (),
        }
    }
    // Look at directly affected entries in A.
    println!("The following entries in A were directly depending on the above files:");
    for entry_a in input_a.iter_entries() {
        if entry_a.inputs().any(|inp| diff_files.contains(inp.path())) {
            println!("{:#?}", entry_a);
        }
    }

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();

    match opts.operation {
        Operation::Convert(conv) => convert(&conv),
        Operation::Print(print) => print_log(&print),
        Operation::Compare(compare) => compare_logs(&compare),
    }
}
