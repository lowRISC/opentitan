// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use regex::Regex;
use std::io::ErrorKind;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::transport::verilator::stdout;

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
    /// Timeout for starting verilator.
    pub timeout: Duration,
}

pub struct Subprocess {
    child: Child,
    accumulated_output: Arc<Mutex<String>>,
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

        log::info!("Spawning verilator: {:?} {:?}", options.executable, args);

        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let accumulator: Arc<Mutex<String>> = Default::default();
        let stdout = child.stdout.take().unwrap();
        let a = Arc::clone(&accumulator);
        std::thread::spawn(move || stdout::accumulate(stdout, a));

        Ok(Subprocess {
            child,
            accumulated_output: accumulator,
        })
    }

    /// Finds a string within the verilator output.
    /// It is assumed that the [`Regex`] `re` has exactly one capture group.
    pub fn find(&mut self, re: &Regex, deadline: Instant) -> Result<String> {
        // Regex captures_len: Capture group 0 is the full match.  Subsequent
        // capture groups are the individual capture groups in the regex.
        // We expect only one user-specified capture group in the regex,
        // and thus expect a capture length of two.
        assert_eq!(re.captures_len(), 2);
        while deadline > Instant::now() {
            {
                let a = self.accumulated_output.lock().unwrap();
                if let Some(captures) = re.captures(&a.as_str()) {
                    let val = captures.get(1).expect("expected a capture");
                    return Ok(val.as_str().to_owned());
                }
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        Err(anyhow!("Timed out"))
    }

    /// Kill the verilator subprocess.
    pub fn kill(&mut self) -> Result<()> {
        match self.child.kill() {
            Err(error) if error.kind() != ErrorKind::InvalidInput => Err(error.into()),
            _ => Ok(()),
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
            timeout: Duration::from_secs(5),
        };
        Subprocess::from_options(options)
    }

    #[test]
    fn test_find_regex() -> Result<()> {
        let mut subprocess = echo_subprocess()?;
        let regex = Regex::new("abc (.*) def")?;
        let deadline = Instant::now() + Duration::from_secs(5);
        let found = subprocess.find(&regex, deadline)?;
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
