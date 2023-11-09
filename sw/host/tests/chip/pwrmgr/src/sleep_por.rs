// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::Parser;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn sleep_por_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    log::info!("Starting host side");
    let vec = UartConsole::wait_for(&*uart, r"PASS|FAIL|Ready for pad POR", opts.timeout)?;
    match vec[0].as_str() {
        "PASS" => return Err(anyhow!("Cannot pass before getting an exra POR")),
        "FAIL" => return Err(anyhow!("Failure result: {:?}", vec)),
        _ => {}
    };
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let vec = UartConsole::wait_for(&*uart, r"PASS|FAIL|Ready for pad POR", opts.timeout)?;
    match vec[0].as_str() {
        "Ready for pad POR" => Ok(()),
        "PASS" => Ok(()),
        _ => Err(anyhow!("Failure result: {:?}", vec)),
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(sleep_por_test, &opts, &transport);
    Ok(())
}
