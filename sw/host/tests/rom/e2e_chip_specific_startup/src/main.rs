// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::e2e_command::TestCommand;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use std::time::Duration;
use structopt::StructOpt;

mod chip_specific_startup;
use chip_specific_startup::ChipStartup;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "10s",
        help = "Console receive timeout",
    )]
    timeout: Duration,
}

fn test_chip_specific_startup(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // TODO: Should really `opts.init.uart_params.create()` here, but we need to refactor
    // BootstrapOptions first.
    //let uart = opts.init.uart_params.create(&transport)?;
    let uart = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    TestCommand::ChipStartup.send(&*uart)?;
    let response = ChipStartup::recv(&*uart, opts.timeout, false)?;

    // FIXME(cfrantz): ast_init_done should really be true.
    assert!(!response.ast_init_done);
    assert!(response.sram.scr_key_valid);
    assert!(response.sram.scr_key_seed_valid);
    assert!(response.sram.init_done);
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_chip_specific_startup, &opts, &transport);
    Ok(())
}
