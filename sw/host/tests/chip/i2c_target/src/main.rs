// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use std::time::Duration;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::i2c_target::{
    I2cTargetAddress, I2cTransaction,
};
use opentitanlib::uart::console::UartConsole;

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

    #[structopt(
        long,
        default_value = "0",
        help = "Name of the debugger's I2C interface"
    )]
    i2c: String,
}

fn test_set_target_address(_opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    //let i2c = transport.i2c(&opts.i2c)?;
    let address = I2cTargetAddress {
        // Respond to address 0x50.
        id0: 0x50,
        mask0: 0x7f,
        // Respond to addressess 0x70-0x73.
        id1: 0x70,
        mask1: 0x7c,
    };
    address.write(&*uart)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;
    uart.clear_rx_buffer()?;

    execute_test!(test_set_target_address, &opts, &transport);
    Ok(())
}
