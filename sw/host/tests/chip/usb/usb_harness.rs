// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Result};
use clap::Parser;
use std::time::Duration;

use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use usb::UsbOpts;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console/USB timeout; device must be configured and some tests require a
    // small degree of user interaction when invoked manually.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "30s")]
    timeout: Duration,

    /// USB options.
    #[command(flatten)]
    usb: UsbOpts,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Wait until test is running.
    let uart = transport.uart("console")?;
    UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Enable VBUS sense on the board if necessary.
    if opts.usb.vbus_control_available() {
        opts.usb.enable_vbus(&transport, true)?;
    }
    // Sense VBUS if available.
    if opts.usb.vbus_sense_available() {
        ensure!(
            opts.usb.vbus_present(&transport)?,
            "OT USB does not appear to be connected to a host (VBUS not detected)"
        );
    }

    // Simply await the PASS/FAIL indication from the device-side software.
    let vec = UartConsole::wait_for(&*uart, r"(PASS|FAIL)!", opts.timeout)?;
    match vec[0].as_str() {
        "PASS!" => Ok(()),
        _ => Err(anyhow!("Failure result: {:?}", vec)),
    }
}
