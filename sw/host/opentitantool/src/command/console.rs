// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::Args;
use raw_tty::TtyModeGuard;
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::File;
use std::io::IsTerminal;
use std::os::unix::io::AsRawFd;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::uart::UartParams;
use opentitanlib::transport::Capability;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Args)]
pub struct Console {
    #[command(flatten)]
    params: UartParams,

    /// Do not print console start end exit messages.
    #[arg(short, long)]
    quiet: bool,

    /// Log console output to a file.
    #[arg(short, long)]
    logfile: Option<String>,

    /// Send a string into the console at startup.
    #[arg(long)]
    send: Option<String>,

    /// Duration of ROM detection timeout.
    #[arg(short,
    long,
    value_parser = humantime::parse_duration)]
    timeout: Option<Duration>,

    /// Print a timestamp on each line of console output.
    #[arg(long)]
    timestamp: bool,

    /// Exit with success if the specified regex is matched.
    #[arg(long)]
    exit_success: Option<String>,

    /// Exit with failure if the specified regex is matched.
    #[arg(long)]
    exit_failure: Option<String>,
}

impl CommandDispatch for Console {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // We need the UART for the console command to operate.
        transport.capabilities()?.request(Capability::UART).ok()?;
        let mut stdout = std::io::stdout();
        let mut stdin = std::io::stdin();

        // Set up resources specified by the command line parameters.
        let mut console = UartConsole {
            logfile: self.logfile.as_ref().map(File::create).transpose()?,
            timeout: self.timeout,
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
            timestamp: self.timestamp,
            newline: true,
            ..Default::default()
        };

        if !self.quiet {
            println!("Starting interactive console");
            println!("[CTRL+C] to exit.\n");
        }
        let status = {
            // Put the terminal into raw mode.  The tty guard will restore the
            // console settings when it goes out of scope.
            let _stdin_guard = if stdin.is_terminal() {
                let mut guard = TtyModeGuard::new(stdin.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            let _stdout_guard = if stdin.is_terminal() {
                let mut guard = TtyModeGuard::new(stdout.as_raw_fd())?;
                guard.set_raw_mode()?;
                Some(guard)
            } else {
                None
            };
            let uart = self.params.create(transport)?;
            if let Some(send) = self.send.as_ref() {
                log::info!("Sending: {:?}", send);
                uart.write(send.as_bytes())?;
            }
            console.interact(&*uart, Some(&mut stdin), Some(&mut stdout))?
        };
        if !self.quiet {
            println!("\n\nExiting interactive console.");
        }

        match status {
            ExitStatus::None | ExitStatus::CtrlC => Ok(None),
            ExitStatus::Timeout => {
                if console.exit_success.is_some() {
                    // If there was a console exit success condition, then a timeout
                    // represents an error.
                    Err(anyhow!("Console timeout exceeded"))
                } else {
                    // If there was no console exit success condition, then a timeout
                    // is not an error.
                    Ok(None)
                }
            }
            ExitStatus::ExitSuccess => {
                log::info!(
                    "ExitSuccess({:?})",
                    console.captures(status).unwrap().get(0).unwrap().as_str()
                );
                Ok(None)
            }
            ExitStatus::ExitFailure => {
                log::info!(
                    "ExitFailure({:?})",
                    console.captures(status).unwrap().get(0).unwrap().as_str()
                );
                Err(anyhow!("Matched exit_failure expression"))
            }
        }
    }
}
