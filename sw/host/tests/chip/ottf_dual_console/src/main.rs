// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
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
    #[arg(long, value_parser = humantime::parse_duration, default_value = "20s")]
    timeout: Duration,

    /// Name of the UART interface to connect to the debug OTTF console.
    #[arg(long, default_value = "dut")]
    debug_console: String,
}

fn ottf_dual_console_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let debug_uart = transport.uart(&opts.debug_console)?;

    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    let _ = UartConsole::wait_for(&*uart, r"Main UART console", opts.timeout)?;
    let _ = UartConsole::wait_for(&*debug_uart, r"Second UART console", opts.timeout)?;
    let _ = UartConsole::wait_for(&*uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    execute_test!(ottf_dual_console_test, &opts, &transport);
    Ok(())
}
