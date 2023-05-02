// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use regex::Regex;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program;
use opentitanlib::uart::console::UartConsole;

// use top_earlgrey::top_earlgrey_memory;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
    #[structopt(flatten)]
    jtag: JtagParams,
    /// Path to the program to load
    #[structopt(long)]
    vmem: PathBuf,
}

fn test_sram_load(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    //
    // Connect to the RISC-V TAP
    //
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let jtag = transport.jtag(&opts.jtag)?;
    log::info!("Connecting to RISC-V TAP");
    jtag.connect(JtagTap::RiscvTap)?;
    log::info!("Halting core");
    jtag.halt()?;
    // TODO don't hardcore this value, it depends on the linker script, there has
    // to be a better way
    let sram_load_addr = 0x10001fc4u32; // TODO don't hardcore that
    let sram_stack_top = 0x10020000u32;
    let sram_stack_size = 128;
    let global_pointer = sram_load_addr + 2048;

    load_sram_program::load_and_execute_sram_program(
        &jtag,
        &opts.vmem,
        sram_load_addr,
        sram_stack_top,
        sram_stack_size,
        global_pointer,
    )?;

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
    // TODO at the moment the sram_main just returns from the call which is BAD since it returns to nowhere
    // probably should setup the stack to return to someplace safe and stop the CPU
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
