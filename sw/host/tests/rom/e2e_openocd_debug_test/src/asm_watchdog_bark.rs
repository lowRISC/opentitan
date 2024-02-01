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
use opentitanlib::io::jtag::{JtagTap, RiscvGpr};
use opentitanlib::test_utils::init::InitializeTest;

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

fn asm_watchdog_bark(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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

    // Run until we check whether ROM execution is enabled
    dbg.run_until("kRomStartBootMaybeHalt", opts.breakpoint_timeout)?;

    // Pretend execution is enabled
    dbg.set_pc("kRomStartBootExecEn")?;

    dbg.run_until("kRomStartStoreT1ToBiteThold", opts.breakpoint_timeout)?;

    // Set the bite threshold to UINT32_MAX. We want to exercise that the
    // bark causes control to reach the interrupt handler.
    dbg.write_reg(RiscvGpr::T1, 0xFFFFFFFF)?;

    // Run until right after configuring the watchdog timer
    dbg.run_until("kRomStartWatchdogEnabled", opts.breakpoint_timeout)?;

    dbg.set_pc("kRomStartBootMaybeHalt")?;

    // Wait for the NMI handler to be hit.
    dbg.run_until("_asm_exception_handler", opts.breakpoint_timeout)?;

    dbg.disconnect()?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(asm_watchdog_bark, &opts, &transport);

    Ok(())
}
