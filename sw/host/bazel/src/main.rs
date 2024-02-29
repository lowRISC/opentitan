// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use std::fs::{File, OpenOptions};
use std::io::BufReader;
use std::path::PathBuf;

use exec_log_lib::bazel_exec_log;
use exec_log_lib::exec_log::ExecLog;

use spawn_proto::protos::SpawnExec;

#[derive(Debug, Parser)]
struct Opts {
    exec_log: PathBuf,
    #[arg(long)]
    json_out: Option<PathBuf>,
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
