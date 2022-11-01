// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::bool_assert_comparison)]

use anyhow::{bail, Result};
use regex::Regex;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::spiflash::SpiFlash;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "5s",
        help = "Bootstrap detection timeout",
    )]
    timeout: Duration,
}

fn test_bootstrap_disabled_requested(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_failure: Some(Regex::new(r"bootstrap:1\r\n")?),
        exit_success: Some(Regex::new(r"BFV:0142500d")?),
        ..Default::default()
    };

    log::info!("Applying pin strapping");
    transport.apply_pin_strapping("ROM_BOOTSTRAP")?;
    log::info!("Resetting target");
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };
    // Now check whether the SPI device is responding to status messages
    log::info!("Issuing SPI READ_STATUS");
    let spi = transport.spi("0")?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0xFF);
    Ok(())
}

fn test_bootstrap_disabled_not_requested(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let mut console = UartConsole {
        timeout: Some(opts.timeout),
        exit_failure: Some(Regex::new(r"bootstrap:1\r\n")?),
        exit_success: Some(Regex::new(r"BFV:0142500d")?),
        ..Default::default()
    };

    log::info!("Not applying pin strapping");
    transport.remove_pin_strapping("ROM_BOOTSTRAP")?;
    log::info!("Resetting target");
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Now watch the console for the exit conditions.
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    if result != ExitStatus::ExitSuccess {
        bail!("FAIL: {:?}", result);
    };
    // Now check whether the SPI device is responding to status messages
    log::info!("Issuing SPI READ_STATUS");
    let spi = transport.spi("0")?;
    assert_eq!(SpiFlash::read_status(&*spi)?, 0xFF);
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_bootstrap_disabled_requested, &opts, &transport);
    execute_test!(test_bootstrap_disabled_not_requested, &opts, &transport);
    Ok(())
}
