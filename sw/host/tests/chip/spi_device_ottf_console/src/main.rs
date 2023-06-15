// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::Parser;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(
    long,
    value_parser = humantime::parse_duration,
    default_value = "600s",
    help = "Console receive timeout",
    )]
    timeout: Duration,

    #[arg(
        long,
        default_value = "BOOTSTRAP",
        help = "Name of the SPI interface to connect to the OTTF console."
    )]
    console_spi: String,
}

fn spi_device_console_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_success: Some(Regex::new(r"PASS.*\n")?),
        exit_failure: Some(Regex::new(r"(FAIL|FAULT).*\n")?),
        newline: true,
        ..Default::default()
    };
    let mut stdout = std::io::stdout();
    let spi = transport.spi(&opts.console_spi)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi);
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;
    let result = console.interact(&spi_console_device, None, Some(&mut stdout))?;
    match result {
        ExitStatus::None | ExitStatus::CtrlC => Ok(()),
        ExitStatus::Timeout => {
            if console.exit_success.is_some() {
                Err(anyhow!("Console timeout exceeded"))
            } else {
                Ok(())
            }
        }
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
    execute_test!(spi_device_console_test, &opts, &transport);
    Ok(())
}
