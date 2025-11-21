// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use clap::Parser;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn power_virus_systemtest(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Below is temporary until this test implements the command / response
    // ujson framework.
    let uart = transport.uart("console")?;
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

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running ", opts.timeout)?;

    execute_test!(power_virus_systemtest, &opts, &transport);
    Ok(())
}
