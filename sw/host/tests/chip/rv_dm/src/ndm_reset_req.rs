// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::io::jtag::JtagTap;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

fn test_ndm_reset_req(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // This test requires RV_DM access so first strap and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Enable console and wait for the message.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;

    log::info!("Waiting for \"wait for ndm reset\" message");
    let _ = UartConsole::wait_for(&*uart, "wait for ndm reset", opts.timeout)?;

    // Connect via JTAG and trigger a NDM reset
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    jtag.reset(true)?;

    UartConsole::wait_for(&*uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_ndm_reset_req, &opts, &transport);

    Ok(())
}
