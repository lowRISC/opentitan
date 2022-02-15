// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use erased_serde::Serialize;
use nix::unistd::isatty;
use raw_tty::TtyModeGuard;
use regex::Regex;
use std::any::Any;
use std::fs::File;
use std::io::{Read, Write};
use std::os::unix::io::AsRawFd;
use std::time::{Duration, Instant};
use structopt::StructOpt;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::uart::{Uart, UartParams};
use opentitanlib::transport::Capability;
use opentitanlib::util::file;

#[derive(Debug, StructOpt)]
pub struct Console {
    #[structopt(flatten)]
    params: UartParams,

    #[structopt(short, long, help = "Do not print console start end exit messages.")]
    quiet: bool,

    #[structopt(short, long, help = "Log console output to a file")]
    logfile: Option<String>,

    #[structopt(short, long, help = "Exit after a timeout in seconds.")]
    timeout: Option<u64>,

    #[structopt(long, help = "Exit with success if the specified regex is matched.")]
    exit_success: Option<String>,

    #[structopt(long, help = "Exit with failure if the specified regex is matched.")]
    exit_failure: Option<String>,
}

impl CommandDispatch for Console {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Serialize>>> {
        // We need the UART for the console command to operate.
        transport.capabilities().request(Capability::UART).ok()?;
        let mut stdout = std::io::stdout();
        let mut stdin = std::io::stdin();

        // Set up resources specified by the command line parameters.
        let mut console = InnerConsole {
            logfile: self.logfile.as_ref().map(File::create).transpose()?,
            deadline: self.timeout.map(|t| Instant::now() + Duration::new(t, 0)),
            exit_success: self
                .exit_success
                .as_ref()
                .map(|s| Regex::new(s.as_str()))
                .transpose()?,
            exit_failure: self
                .exit_failure
                .as_ref()
                .map(|s| Regex::new(s.as_str()))
                .transpose()?,
            ..Default::default()
        };

        if !self.quiet {
            println!("Starting interactive console");
            println!("[CTRL+C] to exit.\n");
        }
        {
            // Put the terminal into raw mode.  The tty guard will restore the
            // console settings when it goes out of scope.
            let _stdin_guard = if isatty(stdin.as_raw_fd())? {
                let mut guard = TtyModeGuard::new(stdin.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            let _stdout_guard = if isatty(stdout.as_raw_fd())? {
                let mut guard = TtyModeGuard::new(stdout.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            let uart = self.params.create(transport)?;
            console.interact(&*uart, &mut stdin, &mut stdout)?;
        }
        if !self.quiet {
            println!("\n\nExiting interactive console.");
        }
        Ok(None)
    }
}

#[derive(Default)]
struct InnerConsole {
    logfile: Option<File>,
    deadline: Option<Instant>,
    exit_success: Option<Regex>,
    exit_failure: Option<Regex>,
    buffer: String,
}

enum ExitStatus {
    None,
    ExitSuccess,
    ExitFailure,
}

impl InnerConsole {
    const CTRL_C: u8 = 3;
    const BUFFER_LEN: usize = 1024;

    // Runs an interactive console until CTRL_C is received.
    fn interact(
        &mut self,
        uart: &dyn Uart,
        stdin: &mut (impl Read + AsRawFd),
        stdout: &mut impl Write,
    ) -> Result<()> {
        let mut buf = [0u8; 256];

        loop {
            if let Some(deadline) = self.deadline {
                if Instant::now() > deadline {
                    // If we have an exit success condition, then a timeout
                    // should be an error.
                    if self.exit_success.is_some() {
                        return Err(anyhow!("Console timeout exceeded"));
                    } else {
                        break;
                    }
                }
            }

            // This loop _should_ really use unix `poll` in the conventional way
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
            match self.uart_read(uart, Duration::from_millis(10), stdout)? {
                ExitStatus::None => {}
                ExitStatus::ExitSuccess => {
                    break;
                }
                ExitStatus::ExitFailure => {
                    return Err(anyhow!("Matched exit_failure expression"));
                }
            };

            // Wait for input from the user.
            if file::wait_read_timeout(&*stdin, Duration::from_millis(0)).is_ok() {
                let len = stdin.read(&mut buf)?;
                if len == 1 && buf[0] == InnerConsole::CTRL_C {
                    break;
                }
                uart.write(&buf[..len])?;
            }
        }
        Ok(())
    }

    // Maintain a buffer for the exit regexes to match against.
    fn append_buffer(&mut self, data: &[u8]) {
        self.buffer.push_str(&String::from_utf8_lossy(data));
        while self.buffer.len() > InnerConsole::BUFFER_LEN {
            self.buffer.remove(0);
        }
    }

    // Read from the uart and process the data read.
    fn uart_read(
        &mut self,
        uart: &dyn Uart,
        timeout: Duration,
        stdout: &mut impl Write,
    ) -> Result<ExitStatus> {
        let mut buf = [0u8; 256];
        let len = uart.read_timeout(&mut buf, timeout)?;
        if len > 0 {
            stdout.write_all(&buf[..len])?;
            stdout.flush()?;

            // If we're logging, save it to the logfile.
            if let Some(logfile) = &mut self.logfile {
                logfile.write_all(&buf[..len])?;
            }

            // If we have exit condition regexes check them.
            self.append_buffer(&buf[..len]);
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
        Ok(ExitStatus::None)
    }
}
