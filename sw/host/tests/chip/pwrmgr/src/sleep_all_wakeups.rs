// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use std::time::Duration;

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

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let ioc0_pin = transport.gpio_pin("Ioc0")?;
    loop {
        let gs = UartConsole::wait_for(&*uart, r"Done|Issue WFI to enter sleep ([0-9]+)", opts.timeout)?;
        if gs[0] == "Done" {
            return Ok(());
        }
        assert_eq!(gs.len(), 2, "Expected sleep unit");
        let sleep_case: i32 = gs[1].parse().expect("expected a number");
        match sleep_case {
            0 => {
                ioc0_pin.write(true)?;
                ioc0_pin.write(false)?;
            }
            2 => {
                ioc0_pin.write(false)?;
                ioc0_pin.write(true)?;
            }
            _ => (),
        }
        let gs = UartConsole::wait_for(&*uart, r"Woke up by source ([0-9]+)", opts.timeout)?;
        assert_eq!(gs.len(), 2, "Expected unit number");
        let sleep_case: i32 = gs[1].parse().expect("expected a number");
        match sleep_case {
            0 => ioc0_pin.write(true)?,
            2 => ioc0_pin.write(false)?,
            _ => (),
        }
    }
}
