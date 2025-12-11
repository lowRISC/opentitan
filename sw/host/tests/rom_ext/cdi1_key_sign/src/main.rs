// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

use anyhow::{Context, Result, anyhow};
use clap::Parser;
use regex::Regex;

/// CLI args for this test.
#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Second image (ROM_EXT + Owner FW bundle) to bootstrap.
    #[arg(long)]
    second_bootstrap: PathBuf,

    /// Third image (ROM_EXT + Owner FW bundle) to bootstrap.
    #[arg(long)]
    third_bootstrap: PathBuf,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "30s")]
    timeout: Duration,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    // Bootstrap first ROM_EXT + Owner FW.
    let transport = opts.init.init_target()?;
    let uart = transport.uart("console").context("failed to get UART")?;

    // Wait for owner FW message.
    let _ = UartConsole::wait_for(&*uart, r"Test Owner FW - 0", opts.timeout)?;

    // Bootstrap second ROM_EXT + Owner FW.
    opts.init
        .bootstrap
        .load(&transport, &opts.second_bootstrap)?;

    // Wait for owner FW message.
    let _ = UartConsole::wait_for(&*uart, r"Test Owner FW - 1", opts.timeout)?;

    // Bootstrap second ROM_EXT + Owner FW.
    opts.init
        .bootstrap
        .load(&transport, &opts.third_bootstrap)?;

    // Wait for pass message from owner firmware stage.
    let mut console = UartConsole::new(
        Some(opts.timeout),
        Some(Regex::new(r"PASS.*\n")?),
        Some(Regex::new(r"(FAIL|FAULT).*\n")?),
    );
    let result = console.interact(&*uart, false)?;
    match result {
        ExitStatus::Timeout => Err(anyhow!("Console timeout exceeded")),
        ExitStatus::ExitSuccess => {
            log::info!(
                "ExitSuccess({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Ok(())
        }
        ExitStatus::ExitFailure => {
            log::info!(
                "ExitFailure({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Err(anyhow!("Matched exit_failure expression"))
        }
    }
}
