// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow, bail};
use crc::{CRC_32_ISO_HDLC, Crc};
use mio::{Events, Interest, Poll, Token};
use rand::Rng;
use regex::{Captures, Regex};
use std::fs::File;
use std::io::{ErrorKind, Read, Write};
use std::os::fd::{AsFd, AsRawFd};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime};

use crate::io::console::{ConsoleDevice, ConsoleError};
use crate::uart::console_plugin::ConsolePlugin;
use crate::uart::coverage_plugin::CoveragePlugin;
use crate::util::file;

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
    pub carriage_return: bool,
    pub break_en: bool,
    pub coverage_plugin: CoveragePlugin,
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
pub trait ReadAsFd: Read + AsFd {}
impl<T: Read + AsFd> ReadAsFd for T {}

impl UartConsole {
    const CTRL_B: u8 = 2;
    const CTRL_C: u8 = 3;
    const BUFFER_LEN: usize = 32768;

    // Runs an interactive console until CTRL_C is received.
    pub fn interact<T>(
        &mut self,
        device: &T,
        mut stdin: Option<&mut dyn ReadAsFd>,
        mut stdout: Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if let Some(timeout) = &self.timeout {
            self.deadline = Some(Instant::now() + *timeout);
        }
        if device.supports_nonblocking_read()? {
            return self.interact_mio(device, stdin, stdout);
        }
        loop {
            match self.interact_once(device, &mut stdin, &mut stdout)? {
                ExitStatus::None => {}
                status => return Ok(status),
            }
        }
    }

    // Runs an interactive console until CTRL_C is received.  Uses `mio` library to simultaneously
    // wait for data from UART or from stdin, without need for timeouts and repeated calls.
    fn interact_mio<T>(
        &mut self,
        device: &T,
        mut stdin: Option<&mut dyn ReadAsFd>,
        mut stdout: Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if self.exit_success.as_ref().map(|rx| rx.is_match("")) == Some(true) {
            // For compatibility with non-mio implementation, an `exit_success` regexp which
            // matches the empty string will result in a single read to clear any buffered
            // characters.
            self.uart_read(device, Duration::from_millis(10), &mut stdout)?;
            return Ok(ExitStatus::ExitSuccess);
        }

        // HACK(nbdd0121): do a nonblocking read because the UART buffer may still have data in it.
        // If we wait for mio event now, we might be blocking forever.
        while self.uart_read(device, Duration::from_millis(0), &mut stdout)? {
            if let Some(exit_status) = self.process_buffer()? {
                return Ok(exit_status);
            }
        }

        let mut poll = Poll::new()?;
        let transport_help_token = Self::get_next_token();
        let nonblocking_help = device.nonblocking_help()?;
        nonblocking_help.register_nonblocking_help(poll.registry(), transport_help_token)?;
        let stdin_token = Self::get_next_token();
        if stdin.is_some() {
            poll.registry().register(
                &mut mio::unix::SourceFd(&stdin.as_mut().unwrap().as_fd().as_raw_fd()),
                stdin_token,
                Interest::READABLE,
            )?;
        }
        let uart_token = Self::get_next_token();
        device.register_nonblocking_read(poll.registry(), uart_token)?;

        let mut events = Events::with_capacity(2);
        loop {
            let now = Instant::now();
            let poll_timeout = if let Some(deadline) = &self.deadline {
                if now >= *deadline {
                    return Ok(ExitStatus::Timeout);
                }
                Some(*deadline - now)
            } else {
                None
            };
            match poll.poll(&mut events, poll_timeout) {
                Ok(()) => (),
                Err(err) if err.kind() == ErrorKind::Interrupted => {
                    continue;
                }
                Err(err) => bail!("poll: {}", err),
            }
            for event in events.iter() {
                if event.token() == transport_help_token {
                    nonblocking_help.nonblocking_help()?;
                } else if event.token() == stdin_token {
                    match self.process_input(device, &mut stdin)? {
                        ExitStatus::None => {}
                        status => return Ok(status),
                    }
                } else if event.token() == uart_token {
                    // `mio` convention demands that we keep reading until a read returns zero
                    // bytes, otherwise next `poll()` is not guaranteed to notice more data.
                    while self.uart_read(device, Duration::from_millis(1), &mut stdout)? {
                        if let Some(exit_status) = self.process_buffer()? {
                            return Ok(exit_status);
                        }
                    }
                }
            }
        }
    }

    fn get_next_token() -> Token {
        static TOKEN_COUNTER: AtomicUsize = AtomicUsize::new(0);
        Token(TOKEN_COUNTER.fetch_add(1, Ordering::Relaxed))
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
        if let Some(status) = self.coverage_plugin.exit_status() {
            return Ok(Some(status));
        }

        let exit_result = self.process_exit_regex();
        self.process_coverage_anchor()?;
        Ok(exit_result)
    }

    // Read from the console device and process the data read.
    fn uart_read<T>(
        &mut self,
        device: &T,
        timeout: Duration,
        stdout: &mut Option<&mut dyn Write>,
    ) -> Result<bool>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut buf = [0u8; 1];
        let len = device.console_read(&mut buf, timeout)?;
        if len == 0 {
            return Ok(false);
        }

        // Process the received bytes through plugin chain.
        let buf = buf[..len].to_vec();
        let buf = self.coverage_plugin.process_bytes(buf)?;
        let len = buf.len();
        if len == 0 {
            return Ok(true);
        }

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
                stdout.as_mut().map_or(Ok(()), |out| {
                    out.write_all(if self.newline && !self.carriage_return {
                        b"\r\n"
                    } else {
                        &buf[i..i + 1]
                    })
                })?;
                self.carriage_return = buf[i] == b'\r';
            }
            stdout.as_mut().map_or(Ok(()), |out| out.flush())?;

            // If we're logging, save it to the logfile.
            self.logfile
                .as_mut()
                .map_or(Ok(()), |f| f.write_all(&buf[..len]))?;
        }
        self.append_buffer(&buf[..len]);
        Ok(true)
    }

    fn process_input<T>(
        &mut self,
        device: &T,
        stdin: &mut Option<&mut (dyn ReadAsFd)>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if let Some(ref mut input) = stdin.as_mut() {
            while file::wait_read_timeout(&input.as_fd(), Duration::from_millis(0)).is_ok() {
                let mut buf = [0u8; 256];
                let len = input.read(&mut buf)?;
                if len == 1 {
                    if buf[0] == UartConsole::CTRL_C {
                        return Ok(ExitStatus::CtrlC);
                    }
                    if buf[0] == UartConsole::CTRL_B {
                        self.break_en = !self.break_en;
                        eprint!(
                            "\r\n{} break",
                            if self.break_en { "Setting" } else { "Clearing" }
                        );
                        let b = device.set_break(self.break_en);
                        if b.is_err() {
                            eprint!(": {:?}", b);
                        }
                        eprint!("\r\n");
                        break;
                    }
                }
                if len > 0 {
                    device.console_write(&buf[..len])?;
                } else {
                    break;
                }
            }
        }
        Ok(ExitStatus::None)
    }

    fn interact_once<T>(
        &mut self,
        device: &T,
        stdin: &mut Option<&mut (dyn ReadAsFd)>,
        stdout: &mut Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if let Some(deadline) = &self.deadline {
            if Instant::now() > *deadline {
                return Ok(ExitStatus::Timeout);
            }
        }
        // This _should_ really use unix `poll` in the conventional way
        // to learn when the console or uart file descriptors become ready,
        // but some UART backends will bury their implementation in libusb
        // and make discovering the file descriptor difficult or impossible.
        //
        // As a pragmatic implementation detail, we wait for the UART
        // for a short period of time and then service the console.
        //
        // TODO: as we write more backends, re-evaluate whether there is a
        // better way to approach waiting on the UART and keyboard.

        // Check for input on the uart.
        self.uart_read(device, Duration::from_millis(10), stdout)?;
        if let Some(exit_status) = self.process_buffer()? {
            return Ok(exit_status);
        }
        self.process_input(device, stdin)
    }

    pub fn captures(&self, status: ExitStatus) -> Option<Captures> {
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
        let mut console = UartConsole {
            timestamp: true,
            newline: true,
            timeout: Some(timeout),
            coverage_plugin: CoveragePlugin::default().stop_after_report(),
            ..Default::default()
        };
        let mut stdout = std::io::stdout();
        let result = console.interact(device, None, Some(&mut stdout))?;
        println!();
        match result {
            ExitStatus::ExitSuccess => Ok(()),
            ExitStatus::Timeout => Err(ConsoleError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
        }
    }
}
