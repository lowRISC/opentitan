// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use clap::Args;
use regex::Regex;
use std::any::Any;
use std::fs::File;
use std::io::Write;
use std::marker::Unpin;
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt};

use opentitanlib::app::TransportWrapper;
use opentitanlib::app::command::CommandDispatch;
use opentitanlib::io::console::Broadcaster;
use opentitanlib::io::uart::{Uart, UartParams};
use opentitanlib::transport::Capability;
use opentitanlib::uart::console::{ExitStatus, UartConsole};
use opentitanlib::util::raw_tty::RawTty;

#[derive(Debug, Args)]
pub struct Console {
    #[command(flatten)]
    params: UartParams,

    /// Do not run in interactive mode and forward stdin.
    #[arg(long, default_value = "false")]
    non_interactive: bool,

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

const CTRL_B: u8 = 2;
const CTRL_C: u8 = 3;

/// Takes input from an input stream and send it to a console device. Breaks are handled.
async fn process_input<T, R>(device: &T, stdin: &mut R) -> Result<()>
where
    T: Uart + ?Sized,
    R: AsyncRead + Unpin,
{
    let mut break_en = false;
    let mut buf = [0u8; 256];
    loop {
        let len = stdin.read(&mut buf).await?;
        if len == 1 {
            if buf[0] == CTRL_C {
                return Ok(());
            }
            if buf[0] == CTRL_B {
                break_en = !break_en;
                eprint!(
                    "\r\n{} break",
                    if break_en { "Setting" } else { "Clearing" }
                );
                let b = device.set_break(break_en);
                if b.is_err() {
                    eprint!(": {:?}", b);
                }
                eprint!("\r\n");
                continue;
            }
        }
        device.write(&buf[..len])?;
    }
}

/// Takes input from a console and write to an output.
async fn pipe_output<T, W>(device: &T, w: &mut W) -> Result<()>
where
    T: Uart + ?Sized,
    W: Write,
{
    let mut buf = [0u8; 256];

    loop {
        let len = std::future::poll_fn(|cx| device.poll_read(cx, &mut buf)).await?;
        w.write_all(&buf[..len])?;
    }
}

impl CommandDispatch for Console {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        // We need the UART for the console command to operate.
        transport.capabilities()?.request(Capability::UART).ok()?;

        let uart = self.params.create(transport)?;
        if let Some(send) = self.send.as_ref() {
            log::info!("Sending: {:?}", send);
            uart.write(send.as_bytes())?;
        }

        let mut logfile = self.logfile.as_ref().map(File::create).transpose()?;

        // Set up resources specified by the command line parameters.
        let mut console = UartConsole::new(
            self.timeout,
            self.exit_success
                .as_ref()
                .map(|s| Regex::new(s.as_str()))
                .transpose()?,
            self.exit_failure
                .as_ref()
                .map(|s| Regex::new(s.as_str()))
                .transpose()?,
        );

        // Put the terminal into raw mode.  The tty guard will restore the
        // console settings when it goes out of scope.
        let mut stdin = if self.non_interactive {
            None
        } else {
            Some(RawTty::new(tokio::io::stdin())?)
        };

        if !self.non_interactive {
            eprint!("Starting interactive console\r\n");
            eprint!("[CTRL+C] to exit.\r\n\r\n");
        }

        let status = transport.relinquish_exclusive_access(|| {
            opentitanlib::util::runtime::block_on(async {
                let uart_rx = Broadcaster::new(uart.clone());

                let tx = async {
                    if let Some(stdin) = stdin.as_mut() {
                        process_input(&*uart, stdin).await
                    } else {
                        std::future::pending().await
                    }
                };

                let log_to_file = async {
                    if let Some(file) = logfile.as_mut() {
                        pipe_output(&uart_rx.clone(), file).await
                    } else {
                        std::future::pending().await
                    }
                };

                let log_to_output = async {
                    if !self.timestamp {
                        // If we want timestamp (similar to how FPGA tests log their outputs),
                        // we can defer this to `UartConsole::interact`. Otherwise pipe to stdout directly.
                        pipe_output(&uart_rx.clone(), &mut std::io::stdout()).await
                    } else {
                        std::future::pending().await
                    }
                };

                let rx = async { console.interact_async(&uart_rx, !self.timestamp).await };

                Result::<_>::Ok(tokio::select! {
                    v = tx => Err(v?),
                    v = log_to_file => Err(v?),
                    v = log_to_output => Err(v?),
                    v = rx => Ok(v?),
                })
            })
        })??;

        // Bring us out from raw mode early.
        drop(stdin);

        if !self.non_interactive {
            eprintln!("\n\nExiting interactive console.");
        }

        match status {
            Err(()) => Ok(None),
            Ok(ExitStatus::Timeout) => {
                if self.exit_success.is_some() {
                    // If there was a console exit success condition, then a timeout
                    // represents an error.
                    Err(anyhow!("Console timeout exceeded"))
                } else {
                    // If there was no console exit success condition, then a timeout
                    // is not an error.
                    Ok(None)
                }
            }
            Ok(ExitStatus::ExitSuccess) => {
                log::info!(
                    "ExitSuccess({:?})",
                    console
                        .captures(ExitStatus::ExitSuccess)
                        .unwrap()
                        .get(0)
                        .unwrap()
                        .as_str()
                );
                Ok(None)
            }
            Ok(ExitStatus::ExitFailure) => {
                log::info!(
                    "ExitFailure({:?})",
                    console
                        .captures(ExitStatus::ExitFailure)
                        .unwrap()
                        .get(0)
                        .unwrap()
                        .as_str()
                );
                Err(anyhow!("Matched exit_failure expression"))
            }
        }
    }
}
