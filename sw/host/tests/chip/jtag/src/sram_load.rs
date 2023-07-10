// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use regex::Regex;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{ExecutionMode, SramProgramParams};
use opentitanlib::uart::console::UartConsole;

// use top_earlgrey::top_earlgrey_memory;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(flatten)]
    sram_program: SramProgramParams,
}

fn test_sram_load(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    //
    // Connect to the RISC-V TAP
    //
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let jtag = opts.init.jtag_params.create(transport)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;
    log::info!("Halting core");
    jtag.halt()?;

    opts.sram_program
        .load_and_execute(&jtag, ExecutionMode::Jump)?;

    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(
            r"sram_program\.c:\d+\] PC: 0x1000[0-2][0-9a-f]{3}, SRAM: \[0x10000000, 0x10020000\)",
        )?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    log::info!("result: {:?}", result);
    jtag.halt()?;
    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_sram_load, &opts, &transport);

    Ok(())
}
