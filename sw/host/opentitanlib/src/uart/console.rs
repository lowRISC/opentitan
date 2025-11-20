// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use regex::{Captures, Regex};
use std::fs::File;
use std::io::Write;
use std::os::fd::AsFd;
use std::time::{Duration, Instant, SystemTime};

use tokio::io::AsyncReadExt;

use crate::io::console::{ConsoleDevice, ConsoleError};

pub struct UartConsole {
    pub logfile: Option<File>,
    timeout: Option<Duration>,
    deadline: Option<Instant>,
    exit_success: Option<Regex>,
    exit_failure: Option<Regex>,
    pub timestamp: bool,
    buffer: String,
    newline: bool,
    break_en: bool,
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

    pub fn new(
        timeout: Option<Duration>,
        exit_success: Option<Regex>,
        exit_failure: Option<Regex>,
    ) -> Self {
        Self {
            logfile: None,
            timeout,
            deadline: None,
            exit_success,
            exit_failure,
            timestamp: true,
            buffer: String::new(),
            newline: true,
            break_en: false,
        }
    }

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
                if self
                    .exit_success
                    .as_ref()
                    .map(|rx| rx.is_match(&self.buffer))
                    == Some(true)
                {
                    return Ok(ExitStatus::ExitSuccess);
                }
                if self
                    .exit_failure
                    .as_ref()
                    .map(|rx| rx.is_match(&self.buffer))
                    == Some(true)
                {
                    return Ok(ExitStatus::ExitFailure);
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

    // Maintain a buffer for the exit regexes to match against.
    fn append_buffer(&mut self, data: &[u8]) {
        self.buffer.push_str(&String::from_utf8_lossy(data));
        while self.buffer.len() > UartConsole::BUFFER_LEN {
            self.buffer.remove(0);
        }
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
        let len = std::future::poll_fn(|cx| device.poll_read(cx, effective_buf)).await?;
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
                device.write(&buf[..len])?;
            }
        }
    }

    pub fn captures(&self, status: ExitStatus) -> Option<Captures<'_>> {
        match status {
            ExitStatus::ExitSuccess => self
                .exit_success
                .as_ref()
                .and_then(|rx| rx.captures(&self.buffer)),
            ExitStatus::ExitFailure => self
                .exit_failure
                .as_ref()
                .and_then(|rx| rx.captures(&self.buffer)),
            _ => None,
        }
    }

    /// Wait on the console until the regex matches the input.
    ///
    /// The input is processed one byte at a time, and is accumulated until match happens.
    pub fn wait_for_bytes<T>(device: &T, rx: &str, timeout: Duration) -> Result<Vec<String>>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut console = UartConsole::new(Some(timeout), Some(Regex::new(rx)?), None);
        let mut stdout = std::io::stdout();
        let result = console.interact(device, None, Some(&mut stdout))?;
        println!();
        match result {
            ExitStatus::ExitSuccess => {
                let caps = console.captures(ExitStatus::ExitSuccess).expect("capture");
                let mut vec = Vec::new();
                for c in caps.iter() {
                    match c {
                        None => vec.push(String::new()),
                        _ => vec.push(c.unwrap().as_str().to_owned()),
                    }
                }
                Ok(vec)
            }
            ExitStatus::Timeout => Err(ConsoleError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
        }
    }

    /// Wait on the console until the regex matches the input.
    ///
    /// The input is processed one line at a time. Lines that does not match the input is discarded.
    pub fn wait_for<T>(device: &T, rx: &str, timeout: Duration) -> Result<Vec<String>>
    where
        T: ConsoleDevice + ?Sized,
    {
        // TODO: Optimize me to read a full line first.
        let mut v = Self::wait_for_bytes(device, &format!("({rx}).*\n"), timeout)?;
        v.remove(0);
        Ok(v)
    }
}
