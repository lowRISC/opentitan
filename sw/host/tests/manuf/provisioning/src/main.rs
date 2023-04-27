// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::UartRecv;
use opentitanlib::uart::console::UartConsole;

mod provisioning_data;
use provisioning_data::ManufProvisioning;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "600s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

fn provisioning(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Get UART, set flow control, and wait for for test to start running.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Wait for exported data to be transimitted over the console.
    let export_data = ManufProvisioning::recv(&*uart, opts.timeout, false)?;
    log::info!("{:#x?}", export_data);

    // TODO: parse RMA unlock token, decrypt it, and try to issue an LC transition.
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(provisioning, &opts, &transport);
    Ok(())
}
