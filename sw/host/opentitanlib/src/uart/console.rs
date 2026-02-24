// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow, bail};
use mio::{Events, Interest, Poll, Token};
use regex::{Captures, Regex};
use std::io::{ErrorKind, Read, Write};
use std::os::fd::{AsFd, AsRawFd};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::io::console::{ConsoleDevice, ConsoleError};
use crate::uart::console_plugin::ConsolePlugin;
use crate::uart::coverage_plugin::CoveragePlugin;
use crate::uart::exit_plugin::ExitPlugin;
use crate::uart::logging_plugin::LoggingPlugin;
use crate::util::file;

#[derive(Default)]
pub struct UartConsole {
    pub timeout: Option<Duration>,
    pub deadline: Option<Instant>,
    pub exit_success: Option<Regex>,
    pub exit_failure: Option<Regex>,
    pub break_en: bool,
    pub coverage_plugin: CoveragePlugin,
    pub logging_plugin: LoggingPlugin,
    pub exit_plugin: ExitPlugin,
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

    // Runs an interactive console until CTRL_C is received.
    pub fn interact<T>(
        &mut self,
        device: &T,
        mut stdin: Option<&mut dyn ReadAsFd>,
        mut _stdout: Option<&mut dyn Write>,
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        // Migrate to new plugin-based interface
        if self.exit_success.is_some() || self.exit_failure.is_some() {
            self.exit_plugin = ExitPlugin::default()
                .exit_success(self.exit_success.clone())
                .exit_failure(self.exit_failure.clone());
        }

        if let Some(timeout) = &self.timeout {
            self.deadline = Some(Instant::now() + *timeout);
        }
        if device.supports_nonblocking_read()? {
            return self.interact_mio(device, stdin);
        }
        loop {
            match self.interact_once(device, &mut stdin)? {
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
    ) -> Result<ExitStatus>
    where
        T: ConsoleDevice + ?Sized,
    {
        // HACK(nbdd0121): do a nonblocking read because the UART buffer may still have data in it.
        // If we wait for mio event now, we might be blocking forever.
        while self.uart_read(device, Duration::from_millis(0))? {
            if let Some(exit_status) = self.exit_status() {
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
                    while self.uart_read(device, Duration::from_millis(1))? {
                        if let Some(exit_status) = self.exit_status() {
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

    fn exit_status(&mut self) -> Option<ExitStatus> {
        if let Some(status) = self.coverage_plugin.exit_status() {
            return Some(status);
        }
        if let Some(status) = self.logging_plugin.exit_status() {
            return Some(status);
        }
        if let Some(status) = self.exit_plugin.exit_status() {
            return Some(status);
        }
        None
    }

    // Read from the console device and process the data read.
    fn uart_read<T>(&mut self, device: &T, timeout: Duration) -> Result<bool>
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
        let buf = self.logging_plugin.process_bytes(buf)?;
        let _buf = self.exit_plugin.process_bytes(buf)?;
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
        self.uart_read(device, Duration::from_millis(10))?;
        if let Some(exit_status) = self.exit_status() {
            return Ok(exit_status);
        }
        self.process_input(device, stdin)
    }

    pub fn captures(&self, status: ExitStatus) -> Option<Captures> {
        self.exit_plugin.captures(status)
    }

    pub fn wait_for<T>(device: &T, rx: &str, timeout: Duration) -> Result<Vec<String>>
    where
        T: ConsoleDevice + ?Sized,
    {
        let mut console = UartConsole {
            timeout: Some(timeout),
            exit_plugin: ExitPlugin::default().exit_success(Some(Regex::new(rx)?)),
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
