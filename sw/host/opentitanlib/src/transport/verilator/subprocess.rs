// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::util::file;
use anyhow::Result;
use log::info;
use regex::Regex;
use std::io::Read;
use std::process::{Child, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

/// Verilator startup options.
pub struct Options {
    /// The verilator executable.
    pub executable: String,
    /// The ROM image used to boot the CPU.
    pub rom_image: String,
    /// The flash image stored in internal flash memory.
    pub flash_image: String,
    /// The OTP settings.
    pub otp_image: String,
    /// Any extra arguments to verilator.
    pub extra_args: Vec<String>,
}

pub struct Subprocess {
    child: Child,
    stdout: ChildStdout,
    accumulated_output: String,
}

impl Subprocess {
    /// Starts a verilator [`Subprocess`] based on [`Options`].
    pub fn from_options(options: Options) -> Result<Self> {
        let mut command = Command::new(&options.executable);
        let mut args = Vec::new();

        if !options.rom_image.is_empty() {
            args.push(format!("--meminit=rom,{}", options.rom_image));
        }
        if !options.flash_image.is_empty() {
            args.push(format!("--meminit=flash,{}", options.flash_image));
        }
        if !options.otp_image.is_empty() {
            args.push(format!("--meminit=otp,{}", options.otp_image));
        }
        args.extend_from_slice(&options.extra_args);
        command.args(&args[..]);

        info!("Spawning verilator: {:?} {:?}", options.executable, args);

        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let stdout = child.stdout.take().unwrap();
        Ok(Subprocess {
            child,
            stdout,
            accumulated_output: String::default(),
        })
    }

    /// Accumulates output from verilator's `stdout`.
    pub fn accumulate(&mut self, timeout: Duration) -> Result<()> {
        let mut buf = [0u8; 256];
        file::wait_read_timeout(&self.stdout, timeout)?;
        let n = self.stdout.read(&mut buf)?;
        let s = String::from_utf8_lossy(&buf[..n]);
        self.accumulated_output.push_str(&s);
        Ok(())
    }

    /// Finds a string within the verilator output.
    /// It is assumed that the [`Regex`] `re` has exactly one capture.
    pub fn find(&mut self, re: &Regex, timeout: Duration) -> Result<String> {
        assert_eq!(re.captures_len(), 1);
        let deadline = Instant::now() + timeout;
        loop {
            if let Some(captures) = re.captures(&self.accumulated_output) {
                let val = captures.get(1).expect("expected a capture");
                return Ok(val.as_str().to_owned());
            } else {
                self.accumulate(deadline.saturating_duration_since(Instant::now()))?;
            }
        }
    }

    /// Kill the verilator subprocess.
    pub fn kill(&mut self) -> Result<()> {
        self.child.kill()?;
        Ok(())
    }
}
