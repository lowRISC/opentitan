// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Parser, Subcommand, ValueEnum};

use std::fs::{File, OpenOptions};
use std::io::BufReader;
use std::path::PathBuf;

use exec_log_lib::bazel_exec_log;
use exec_log_lib::exec_log::ExecLog;

use spawn_proto::protos::SpawnExec;

/// File format of the log file.
#[derive(Debug, ValueEnum)]
#[serde(rename_all = "kebab-case")]
enum Format {
    /// Automatically guess the format based on the extension.
    Auto,
    /// Bazel binary execution log (protobuf).
    BazelBin,
    /// Opentitan json format.
    OtJson,
}

/// Operation to perform.
#[derive(Debug, Subcommand)]
#[serde(rename_all = "kebab-case")]
enum Operation {
    /// Convert between formats.
    Convert(ConvertCommand),
    /// Print the log.
    Print(PrintCommand),
}

/// Conversion command.
#[derive(Debug, Args)]
struct ConvertCommand {
    /// Input format.
    #[arg(long, default_value_t = Format::Auto)]
    in_format: Format,
    /// Output format.
    #[arg(long, default_value_t = Format::Auto)]
    out_format: Format,
    /// Input file.
    input: PathBuf,
    /// Output file.
    output: PathBuf,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    operation: Operation,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    let file = File::open(opts.exec_log)?;
    let mut reader = BufReader::with_capacity(10_000_000, file);
    let mut buf = Vec::<u8>::new();

    let mut nr_msg = 0;
    let elapsed = std::time::Instant::now();
    let mut msg = SpawnExec::default();

    let mut exec_log = ExecLog::new();

    loop {
        if !bazel_exec_log::read_spawn_exec(&mut reader, &mut msg, &mut buf)? {
            break;
        };
        // println!("msg: {msg:#?}");
        exec_log.add_bazel_entry(&msg);
        nr_msg += 1;
    }
    println!("parsing took {}ms", elapsed.elapsed().as_millis());
    println!("number of messages: {nr_msg}");
    println!("max message size: {}", buf.capacity());

    println!("{exec_log:#?}");

    if let Some(json_out) = opts.json_out {
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(json_out)?;
        serde_json::to_writer(&file, &exec_log)?;
    }

    Ok(())
}
