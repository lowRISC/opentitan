// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow, bail};
use crc::{CRC_32_ISO_HDLC, Crc};
use rand::Rng;
use regex::{Captures, Regex};
use std::fs::File;
use std::io::Write;
use std::os::fd::AsFd;
use std::time::{Duration, Instant, SystemTime};

use tokio::io::AsyncReadExt;

use crate::io::console::{ConsoleDevice, ConsoleError};

const COVERAGE_START_ANCHOR: &str = "== COVERAGE PROFILE START ==\r\n";
const COVERAGE_END_ANCHOR: &str = "== COVERAGE PROFILE END ==\r\n";
const COVERAGE_SKIP_ANCHOR: &str = "== COVERAGE PROFILE SKIP ==\r\n";

#[derive(Default, PartialEq)]
pub enum BufferMode {
    #[default]
    Normal,
    Coverage,
}

#[derive(Default)]
pub struct UartConsole {
    pub logfile: Option<File>,
    pub timeout: Option<Duration>,
    pub deadline: Option<Instant>,
    pub exit_success: Option<Regex>,
    pub exit_failure: Option<Regex>,
    pub timestamp: bool,
    pub buffer_mode: BufferMode,
    pub normal_buffer: String,
    pub coverage_buffer: String,
    pub newline: bool,
    pub break_en: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExitStatus {
    None,
    CtrlC,
    Timeout,
    ExitSuccess,
    ExitFailure,
}

// Creates a vtable for implementors of Read and AsFd traits.
pub trait ReadAsFd: tokio::io::AsyncRead + AsFd + std::marker::Unpin {}
impl<T: tokio::io::AsyncRead + AsFd + std::marker::Unpin> ReadAsFd for T {}

impl UartConsole {
    const CTRL_B: u8 = 2;
    const CTRL_C: u8 = 3;
    const BUFFER_LEN: usize = 32768;

    // Runs an interactive console until CTRL_C is received.
    pub fn interact<T>(
        &mut self,
        device: &T,
        stdin: Option<&mut dyn ReadAsFd>,
        stdout: Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if let Some(timeout) = &self.timeout {
            self.deadline = Some(Instant::now() + *timeout);
        }
        crate::util::runtime::block_on(self.interact_async(device, stdin, stdout))
    }

    // Runs an interactive console until CTRL_C is received.  Uses `mio` library to simultaneously
    // wait for data from UART or from stdin, without need for timeouts and repeated calls.
    async fn interact_async<T>(
        &mut self,
        device: &T,
        mut stdin: Option<&mut dyn ReadAsFd>,
        mut stdout: Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut break_en = self.break_en;
        let deadline = self.deadline;
        let tx = async {
            if let Some(stdin) = stdin.as_mut() {
                Self::process_input(&mut break_en, device, stdin).await
            } else {
                std::future::pending().await
            }
        };
        let rx = async {
            loop {
                self.uart_read(device, &mut stdout).await?;
                if let Some(exit_status) = self.process_buffer()? {
                    return Ok(exit_status);
                }
            }
        };
        let deadline = async {
            if let Some(deadline) = deadline {
                tokio::time::sleep_until(tokio::time::Instant::from_std(deadline)).await;
            } else {
                std::future::pending().await
            }
        };

        let r = tokio::select! {
            v = tx => v,
            v = rx => v,
            _ = deadline => Ok(ExitStatus::Timeout),
        };
        self.break_en = break_en;
        r
    }

    /// Returns `true` if any regular expressions are used to match the streamed output.  If so,
    /// then this struct will keep a window of the most recent output, and take care not to read
    /// any more characters from the underlying stream should one of the regular expressions
    /// match.
    fn uses_regex(&self) -> bool {
        self.exit_success.is_some() || self.exit_failure.is_some()
    }

    // Returns a reference to the currently active buffer (normal or coverage).
    fn get_active_buffer(&self) -> &str {
        match self.buffer_mode {
            BufferMode::Normal => &self.normal_buffer,
            BufferMode::Coverage => &self.coverage_buffer,
        }
    }

    // Returns a mutable reference to the currently active buffer (normal or coverage).
    fn get_active_buffer_mut(&mut self) -> &mut String {
        match self.buffer_mode {
            BufferMode::Normal => &mut self.normal_buffer,
            BufferMode::Coverage => &mut self.coverage_buffer,
        }
    }

    // Maintain a buffer for the exit regexes to match against.
    fn append_buffer(&mut self, data: &[u8]) {
        let active_buffer = self.get_active_buffer_mut();
        active_buffer.push_str(&String::from_utf8_lossy(data));
        while active_buffer.len() > UartConsole::BUFFER_LEN {
            active_buffer.remove(0);
        }
    }

    // Remove the last n bytes from the active buffer
    fn pop_buffer(&mut self, n: usize) {
        let active_buffer = self.get_active_buffer_mut();
        let new_len = active_buffer.len().saturating_sub(n);
        active_buffer.truncate(new_len);
    }

    fn process_coverage_anchor(&mut self) -> Result<()> {
        let active_buffer = self.get_active_buffer();
        if active_buffer.ends_with(COVERAGE_START_ANCHOR) {
            self.pop_buffer(COVERAGE_START_ANCHOR.len());
            if self.buffer_mode == BufferMode::Coverage {
                eprintln!("WARN: Got unterminated coverage block:");
                eprintln!("{}", self.coverage_buffer);
            }
            self.buffer_mode = BufferMode::Coverage;
            self.coverage_buffer.clear();
        } else if active_buffer.ends_with(COVERAGE_END_ANCHOR) {
            self.pop_buffer(COVERAGE_END_ANCHOR.len());
            if self.buffer_mode == BufferMode::Coverage {
                self.process_coverage_data()?;
            } else {
                eprintln!("WARN: Got unexpected coverage end indicator!");
            }
            self.buffer_mode = BufferMode::Normal;
            self.coverage_buffer.clear();
        } else if active_buffer.ends_with(COVERAGE_SKIP_ANCHOR) {
            self.pop_buffer(COVERAGE_SKIP_ANCHOR.len());
            if self.buffer_mode == BufferMode::Coverage {
                eprintln!("WARN: Got unterminated coverage block:");
                eprintln!("{}", self.coverage_buffer);
            }
            self.buffer_mode = BufferMode::Normal;
            self.coverage_buffer.clear();
        }
        Ok(())
    }

    fn process_coverage_data(&mut self) -> Result<()> {
        let response = hex::decode(&self.coverage_buffer)?;
        if response.len() < 4 {
            bail!(
                "Coverage from the device is too short: {} bytes",
                response.len()
            );
        }

        let (response, crc) = response.split_at(response.len() - 4);
        let crc = u32::from_le_bytes(crc.try_into()?);
        let actual = Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(response);
        if crc != actual {
            bail!("Coverage corrupted: crc = {crc:08x}, actual = {actual:08x}");
        }

        let path = std::env::var("LLVM_PROFILE_FILE").unwrap_or("./default.profraw".to_owned());
        let path = path.replace("%h", "test.on.device");
        let path = path.replace("%p", &rand::thread_rng().r#gen::<u32>().to_string());
        let path = path.replace("%m", "0");
        let path = path.replace(".profraw", ".xprofraw");

        println!("Saving coverage profile to {path}");
        std::fs::write(path, response)?;

        Ok(())
    }

    fn process_exit_regex(&self) -> Option<ExitStatus> {
        let active_buffer = self.get_active_buffer();

        if self
            .exit_success
            .as_ref()
            .map(|rx| rx.is_match(active_buffer))
            == Some(true)
        {
            return Some(ExitStatus::ExitSuccess);
        }
        if self
            .exit_failure
            .as_ref()
            .map(|rx| rx.is_match(active_buffer))
            == Some(true)
        {
            return Some(ExitStatus::ExitFailure);
        }
        None
    }

    fn process_buffer(&mut self) -> Result<Option<ExitStatus>> {
        let exit_result = self.process_exit_regex();
        self.process_coverage_anchor()?;
        Ok(exit_result)
    }

    // Read from the console device and process the data read.
    async fn uart_read<T>(&mut self, device: &T, stdout: &mut Option<&mut dyn Write>) -> Result<()>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut buf = [0u8; 1024];
        let effective_buf = if self.uses_regex() {
            // Read one byte at a time when matching, to avoid the risk of consuming output past a
            // match.
            &mut buf[..1]
        } else {
            &mut buf
        };
        let len = std::future::poll_fn(|cx| device.console_poll_read(cx, effective_buf)).await?;
        if self.buffer_mode == BufferMode::Normal {
            for i in 0..len {
                if self.timestamp && self.newline {
                    let t = humantime::format_rfc3339_millis(SystemTime::now());
                    stdout.as_mut().map_or(Ok(()), |out| {
                        out.write_fmt(format_args!("[{}  console]", t))
                    })?;
                    self.newline = false;
                }
                self.newline = buf[i] == b'\n';
                stdout
                    .as_mut()
                    .map_or(Ok(()), |out| out.write_all(&buf[i..i + 1]))?;
            }
            stdout.as_mut().map_or(Ok(()), |out| out.flush())?;

            // If we're logging, save it to the logfile.
            self.logfile
                .as_mut()
                .map_or(Ok(()), |f| f.write_all(&buf[..len]))?;
        }
        if self.uses_regex() {
            self.append_buffer(&buf[..len]);
        }
        Ok(())
    }

    async fn process_input<T>(
        break_en: &mut bool,
        device: &T,
        stdin: &mut dyn ReadAsFd,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        loop {
            let mut buf = [0u8; 256];
            let len = stdin.read(&mut buf).await?;
            if len == 1 {
                if buf[0] == UartConsole::CTRL_C {
                    return Ok(ExitStatus::CtrlC);
                }
                if buf[0] == UartConsole::CTRL_B {
                    *break_en = !*break_en;
                    eprint!(
                        "\r\n{} break",
                        if *break_en { "Setting" } else { "Clearing" }
                    );
                    let b = device.set_break(*break_en);
                    if b.is_err() {
                        eprint!(": {:?}", b);
                    }
                    eprint!("\r\n");
                    continue;
                }
            }
            if len > 0 {
                device.console_write(&buf[..len])?;
            }
        }
    }

    pub fn captures(&self, status: ExitStatus) -> Option<Captures<'_>> {
        let active_buffer = self.get_active_buffer();
        match status {
            ExitStatus::ExitSuccess => self
                .exit_success
                .as_ref()
                .and_then(|rx| rx.captures(active_buffer)),
            ExitStatus::ExitFailure => self
                .exit_failure
                .as_ref()
                .and_then(|rx| rx.captures(active_buffer)),
            _ => None,
        }
    }

    pub fn wait_for<T>(device: &T, rx: &str, timeout: Duration) -> Result<Vec<String>>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut console = UartConsole {
            timestamp: true,
            newline: true,
            timeout: Some(timeout),
            exit_success: Some(Regex::new(rx)?),
            ..Default::default()
        };
        let mut stdout = std::io::stdout();
        let result = console.interact(device, None, Some(&mut stdout))?;
        println!();
        match result {
            ExitStatus::ExitSuccess => {
                let mut vec = Vec::new();
                if let Some(caps) = console.captures(ExitStatus::ExitSuccess) {
                    for c in caps.iter() {
                        match c {
                            None => vec.push(String::new()),
                            _ => vec.push(c.unwrap().as_str().to_owned()),
                        }
                    }
                }
                Ok(vec)
            }
            ExitStatus::Timeout => Err(ConsoleError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
        }
    }

    pub fn wait_for_coverage<T>(device: &T, timeout: Duration) -> Result<()>
    where
        T: ConsoleDevice + ?Sized,
    {
        let anchor =
            regex::escape(COVERAGE_END_ANCHOR) + "|" + &regex::escape(COVERAGE_SKIP_ANCHOR);

        Self::wait_for(device, &anchor, timeout)?;
        Ok(())
    }
}
