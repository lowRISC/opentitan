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

fn sleep_all_resets_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let ioc0_pin = transport.gpio_pin("Ioc0")?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    loop {
        let vec = UartConsole::wait_for(&*uart, r"PASS|FAIL|Sysrst reset in", opts.timeout)?;
        log::info!("read from uart: {}", vec[0]);
        match vec[0].as_str() {
            "PASS" => return Ok(()),
            "FAIL" => return Err(anyhow!("Failure result: {:?}", vec)),
            _ => {}
        };
        log::info!("Sending rst via ioc0");
        ioc0_pin.write(true)?;
        // Hold it up for some time before a transition low.
        std::thread::sleep(Duration::from_millis(1));
        ioc0_pin.write(false)?;
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(sleep_all_resets_test, &opts, &transport);
    Ok(())
}
