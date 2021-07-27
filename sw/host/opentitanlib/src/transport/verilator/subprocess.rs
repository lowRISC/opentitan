// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::util::file;
use anyhow::Result;
use log::info;
use regex::Regex;
use std::io::{ErrorKind, Read};
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
    /// It is assumed that the [`Regex`] `re` has exactly one capture group.
    pub fn find(&mut self, re: &Regex, timeout: Duration) -> Result<String> {
        // Regex captures_len: Capture group 0 is the full match.  Subsequent
        // capture groups are the individual capture groups in the regex.
        // We expect only one user-specified capture group in the regex,
        // and thus expect a capture length of two.
        assert_eq!(re.captures_len(), 2);
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
        match self.child.kill() {
            Ok(_) => Ok(()),
            Err(error) => {
                if error.kind() == ErrorKind::InvalidInput {
                    // Don't care if the child has already exited.
                    Ok(())
                } else {
                    Err(error.into())
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn echo_subprocess() -> Result<Subprocess> {
        let options = Options {
            executable: "/bin/echo".to_owned(),
            rom_image: "".to_owned(),
            flash_image: "".to_owned(),
            otp_image: "".to_owned(),
            extra_args: vec!["abc 123 def 456".to_owned()],
        };
        Subprocess::from_options(options)
    }

    #[test]
    fn test_find_regex() -> Result<()> {
        let mut subprocess = echo_subprocess()?;
        let regex = Regex::new("abc (.*) def")?;
        let found = subprocess.find(&regex, Duration::from_millis(5000))?;
        assert_eq!(found, "123");
        Ok(())
    }

    #[test]
    fn test_kill() -> Result<()> {
        let mut subprocess = echo_subprocess()?;
        subprocess.kill()?;
        Ok(())
    }
}
