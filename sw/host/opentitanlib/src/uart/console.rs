// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Result};
use mio::{Events, Interest, Poll, Token};
use regex::{Captures, Regex};
use std::fs::File;
use std::io::{ErrorKind, Read, Write};
use std::os::unix::io::AsRawFd;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant, SystemTime};

use crate::io::console::{ConsoleDevice, ConsoleError};
use crate::util::file;

#[derive(Default)]
pub struct UartConsole {
    pub logfile: Option<File>,
    pub timeout: Option<Duration>,
    pub deadline: Option<Instant>,
    pub exit_success: Option<Regex>,
    pub exit_failure: Option<Regex>,
    pub timestamp: bool,
    pub buffer: String,
    pub newline: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExitStatus {
    None,
    CtrlC,
    Timeout,
    ExitSuccess,
    ExitFailure,
}

// Creates a vtable for implementors of Read and AsRawFd traits.
pub trait ReadAsRawFd: Read + AsRawFd {}
impl<T: Read + AsRawFd> ReadAsRawFd for T {}

impl UartConsole {
    const CTRL_C: u8 = 3;
    const BUFFER_LEN: usize = 4096;

    // Runs an interactive console until CTRL_C is received.
    pub fn interact<T>(
        &mut self,
        device: &T,
        mut stdin: Option<&mut dyn ReadAsRawFd>,
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
        mut stdin: Option<&mut dyn ReadAsRawFd>,
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

        let mut poll = Poll::new()?;
        let transport_help_token = Self::get_next_token();
        let nonblocking_help = device.nonblocking_help()?;
        nonblocking_help.register_nonblocking_help(poll.registry(), transport_help_token)?;
        let stdin_token = Self::get_next_token();
        if stdin.is_some() {
            poll.registry().register(
                &mut mio::unix::SourceFd(&stdin.as_mut().unwrap().as_raw_fd()),
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
                }
            }
        }
    }

    fn get_next_token() -> Token {
        static TOKEN_COUNTER: AtomicUsize = AtomicUsize::new(0);
        Token(TOKEN_COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    // Maintain a buffer for the exit regexes to match against.
    fn append_buffer(&mut self, data: &[u8]) {
        self.buffer.push_str(&String::from_utf8_lossy(data));
        while self.buffer.len() > UartConsole::BUFFER_LEN {
            self.buffer.remove(0);
        }
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
        let mut buf = [0u8; 256];
        let len = device.console_read(&mut buf, timeout)?;
        if len == 0 {
            return Ok(false);
        }
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
        self.append_buffer(&buf[..len]);
        Ok(true)
    }

    fn process_input<T>(
        &self,
        device: &T,
        stdin: &mut Option<&mut (dyn ReadAsRawFd)>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        if let Some(ref mut input) = stdin.as_mut() {
            while file::wait_fd_read_timeout(input.as_raw_fd(), Duration::from_millis(0)).is_ok() {
                let mut buf = [0u8; 256];
                let len = input.read(&mut buf)?;
                if len == 1 && buf[0] == UartConsole::CTRL_C {
                    return Ok(ExitStatus::CtrlC);
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
        stdin: &mut Option<&mut (dyn ReadAsRawFd)>,
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
        self.process_input(device, stdin)
    }

    pub fn captures(&self, status: ExitStatus) -> Option<Captures> {
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

    pub fn wait_for<T>(device: &T, rx: &str, timeout: Duration) -> Result<String>
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
                let cap = console.captures(ExitStatus::ExitSuccess).expect("capture");
                let s = cap.get(0).expect("capture group").as_str().to_owned();
                Ok(s)
            }
            ExitStatus::Timeout => Err(ConsoleError::GenericError("Timed Out".into()).into()),
            _ => Err(anyhow!("Impossible result: {:?}", result)),
        }
    }
}
