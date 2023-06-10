// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Result};
use regex::Regex;
use std::io::ErrorKind;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crate::util::printer;

/// Verilator startup options.
pub struct Options {
    /// The verilator executable.
    pub executable: String,
    /// The ROM image used to boot the CPU.
    pub rom_image: String,
    /// The flash images stored in internal flash memory, one file per bank.
    pub flash_images: Vec<String>,
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
        if !options.flash_images.is_empty() {
            let re = Regex::new(r"^(?P<fname>.*?)(:(?P<slot>\d+))?$").unwrap();
            for image in options.flash_images.iter() {
                let groups = re.captures(image).unwrap();
                let image_file = groups.name("fname").unwrap().as_str();
                let slot = match groups.name("slot") {
                    Some(x) => x.as_str().parse::<u8>().unwrap(),
                    None => 0,
                };
                args.push(format!("--meminit=flash{},{}", slot, image_file));
            }
        }
        if !options.otp_image.is_empty() {
            args.push(format!("--meminit=otp,{}", options.otp_image));
        }
        args.extend_from_slice(&options.extra_args);
        command.args(&args[..]);

        log::info!("CWD: {:?}", std::env::current_dir());
        log::info!(
            "Spawning verilator: {:?} {:?}",
            options.executable,
            args.join(" ")
        );

        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let accumulator: Arc<Mutex<String>> = Default::default();
        let stdout = child.stdout.take().unwrap();
        let a = Arc::clone(&accumulator);
        std::thread::spawn(move || {
            printer::accumulate(stdout, concat!(module_path!(), "::stdout"), a)
        });

        Ok(Subprocess {
            child,
            accumulated_output: accumulator,
        })
    }

    /// Finds a string within the verilator output.
    /// It is assumed that the [`Regex`] `re` has zero or one capture groups.
    pub fn find(&self, re: &Regex, deadline: Instant) -> Result<String> {
        // Regex captures_len: Capture group 0 is the full match.  Subsequent
        // capture groups are the individual capture groups in the regex.
        // We expect at most one user-specified capture group in the regex,
        // and thus expect a capture length of at most two.
        let len = re.captures_len();
        ensure!(
            len <= 2,
            "Expected zero or one capture groups, found {}",
            len
        );
        while deadline > Instant::now() {
            {
                let a = self.accumulated_output.lock().unwrap();
                if let Some(captures) = re.captures(a.as_str()) {
                    let val = captures.get(len - 1).expect("expected a capture");
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
            flash_images: vec!["/dev/null:1".to_owned()],
            otp_image: "".to_owned(),
            extra_args: vec!["abc 123 def 456".to_owned()],
            timeout: Duration::from_secs(5),
        };
        Subprocess::from_options(options)
    }

    #[test]
    fn test_find_regex() -> Result<()> {
        let subprocess = echo_subprocess()?;
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
