// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::io::Read;
use std::process::ChildStdout;
use std::sync::{Arc, Mutex};

// The whole point of this module being named `stdout.rs` is so that the log message
// looks like `[<timestamp> INFO ...verilator::stdout] <message>`.

// Accumulates output from verilator's `stdout`.
pub fn accumulate(stdout: ChildStdout, accumulator: Arc<Mutex<String>>) {
    if let Err(e) = worker(stdout, accumulator) {
        log::error!("accumulate error: {:?}", e);
    }
}

fn worker(mut stdout: ChildStdout, accumulator: Arc<Mutex<String>>) -> Result<()> {
    let mut s = String::default();
    loop {
        read(&mut stdout, &mut s)?;
        let mut lines = s.split('\n').collect::<Vec<&str>>();
        let next = if !s.ends_with('\n') {
            // If we didn't read a complete line at the end, save it for the
            // next read.
            lines.pop()
        } else {
            None
        };
        for line in lines {
            log::info!("{}", line);
        }
        accumulator.lock().unwrap().push_str(&s);
        s = next.unwrap_or("").to_string();
    }
}

fn read(stdout: &mut ChildStdout, s: &mut String) -> Result<()> {
    let mut buf = [0u8; 256];
    let n = stdout.read(&mut buf)?;
    s.push_str(&String::from_utf8_lossy(&buf[..n]));
    Ok(())
}
