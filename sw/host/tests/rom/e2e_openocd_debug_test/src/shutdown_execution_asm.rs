// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::debug::elf_debugger::ElfSymbols;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;

use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long)]
    elf: PathBuf,

    /// Breakpoint timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "5s")]
    breakpoint_timeout: Duration,
}

fn shutdown_execution_asm(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    log::info!("Loading symbols from ELF {}", opts.elf.display());
    let sym = ElfSymbols::load_elf(&opts.elf)?;

    // This test requires RV_DM access so first strap and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    let mut dbg = sym.attach(jtag);
    dbg.reset(false)?;

    // Reset PC to the start of main SRAM
    dbg.set_pc(top_earlgrey::SRAM_CTRL_MAIN_RAM_BASE_ADDR as u32)?;

    // Check that the execution hits the exception handler
    dbg.run_until("_asm_exception_handler", opts.breakpoint_timeout)?;

    dbg.disconnect()?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(shutdown_execution_asm, &opts, &transport);

    Ok(())
}
