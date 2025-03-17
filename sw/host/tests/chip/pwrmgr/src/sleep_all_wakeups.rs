// Copyright lowRISC contributors (OpenTitan project).
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

fn sleep_all_wakeups_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let ioc0_pin = transport.gpio_pin("Ioc0")?;
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    loop {
        let vec = UartConsole::wait_for(
            &*uart,
            r"PASS|FAIL|Test ([0-9]+) begin \(([^)]*)\)",
            opts.timeout,
        )?;
        if vec[0].as_str() == "PASS" {
            return Ok(());
        }
        if vec[0].as_str() == "FAIL" {
            return Err(anyhow!("Failure result: {:?}", vec));
        }
        assert_eq!(vec.len(), 3, "Expected sleep unit and name");
        let test_sleep_case: i32 = vec[1].parse().expect("expected a number");
        let test_sleep_name = &vec[2];
        let vec = UartConsole::wait_for(
            &*uart,
            &format!("FAIL|Issue WFI to enter sleep {test_sleep_case}"),
            opts.timeout,
        )?;
        if vec[0].as_str() == "FAIL" {
            return Err(anyhow!("Failure result: {:?}", vec));
        }
        match test_sleep_name.as_str() {
            "SYSRST_CTRL" => {
                ioc0_pin.write(true)?;
                ioc0_pin.write(false)?;
            }
            "PINMUX" => {
                ioc0_pin.write(false)?;
                ioc0_pin.write(true)?;
            }
            _ => (),
        }
        let _ = UartConsole::wait_for(
            &*uart,
            &format!("Woke up by source {test_sleep_case}"),
            opts.timeout,
        )?;
        match test_sleep_name.as_str() {
            "SYSRST_CTRL" => ioc0_pin.write(true)?,
            "PINMUX" => ioc0_pin.write(false)?,
            _ => (),
        }
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(sleep_all_wakeups_test, &opts, &transport);
    Ok(())
}
