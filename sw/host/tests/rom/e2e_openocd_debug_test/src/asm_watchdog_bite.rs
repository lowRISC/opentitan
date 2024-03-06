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

use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long)]
    elf: PathBuf,

    /// Breakpoint timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    breakpoint_timeout: Duration,
}

fn asm_watchdog_bite(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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

    // We don't want the bark to trigger for this test.
    // There's no label before BARK_THOLD is stored, so we need to override the stored value.
    dbg.write_u32(
        top_earlgrey::AON_TIMER_AON_BASE_ADDR as u32
            + opentitanlib::dif::aon_timer::AonTimerReg::WdogBarkThold as u32,
        0xFFFFFFFF,
    )?;

    // Double the bite timeout. The current timeout is too short, causing this test to be flaky.
    let orig_timeout = dbg.read_reg(RiscvGpr::T1)?;
    dbg.write_reg(RiscvGpr::T1, orig_timeout * 2)?;

    // Clear RESET_INFO.
    dbg.write_u32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32
            + opentitanlib::dif::rstmgr::RstmgrReg::ResetInfo as u32,
        0,
    )?;

    dbg.run_until("kRomStartWatchdogEnabled", opts.breakpoint_timeout)?;

    dbg.set_pc("kRomStartBootMaybeHalt")?;

    // Set a breakpoint to ensure the NMI handler is not being hit.
    // If the NMI handler is hit then the PC check below will fail.
    dbg.set_breakpoint("_asm_exception_handler")?;

    // This should trigger the watchdog and cause a reset.
    // Disconnect JTAG, wait for a sufficiently long period to allow reset to complete and reconnect.
    dbg.disconnect()?;
    std::thread::sleep(opts.breakpoint_timeout);
    let jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    dbg = sym.attach(jtag);

    // Check that the execution has stuck after reset at the given known location.
    dbg.halt()?;
    dbg.expect_pc_range("kRomStartBootHalted".."kRomStartBootExecEn")?;

    // Check the reset reason as well
    let reset_info = dbg.read_u32(
        top_earlgrey::RSTMGR_AON_BASE_ADDR as u32
            + opentitanlib::dif::rstmgr::RstmgrReg::ResetInfo as u32,
    )?;

    // Check that the reset is caused by watchdog.
    log::info!("RESET_INFO={:#x}", reset_info);
    assert!(reset_info & u32::from(opentitanlib::dif::rstmgr::DifRstmgrResetInfo::Watchdog) != 0);

    dbg.disconnect()?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(asm_watchdog_bite, &opts, &transport);

    Ok(())
}
