// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::io::Read;
use std::sync::{Arc, Mutex};

// If the logger is configured to use the module's path, the log message will always
// look like `[<timestamp> INFO ...util::printer] <message>` which is inconvenient
// because we loose the source of the message.
// However, if the logger is configured to print the target instead of the module path
// then it will look like `[<timestamp> INFO <target>] <message>`. Since the default
// target is the module's path, this allows for a non-breaking change by configuring
// the logger to always print the target instead of the module.

// Accumulates output from a process's `stdout`.
pub fn accumulate(stdout: impl Read, target: &str, accumulator: Arc<Mutex<String>>) {
    if let Err(e) = worker(stdout, target, accumulator) {
        log::error!("accumulate error: {:?}", e);
    }
}

fn worker(mut stdout: impl Read, target: &str, accumulator: Arc<Mutex<String>>) -> Result<()> {
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
            // see comment at the top of this module
            log::info!(target: target, "{}", line.trim_end_matches('\r'));
        }
        accumulator.lock().unwrap().push_str(&s);
        s = next.unwrap_or("").to_string();
    }
}

fn read(stdout: &mut impl Read, s: &mut String) -> Result<()> {
    let mut buf = [0u8; 256];
    let n = stdout.read(&mut buf)?;
    s.push_str(&String::from_utf8_lossy(&buf[..n]));
    Ok(())
}
