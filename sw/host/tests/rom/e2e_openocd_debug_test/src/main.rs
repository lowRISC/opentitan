// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use opentitanlib::io::uart::Uart;
use regex::Regex;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagTap, RiscvCsr, RiscvGpr};
use opentitanlib::test_utils::elf_debugger::{ElfDebugger, ElfSymbols, SymbolicAddress};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long)]
    elf: PathBuf,

    /// Expect the test to fail.
    ///
    /// When this flag is set, the binary will return successful exit code
    /// if and only if the test fails.
    #[arg(long)]
    expect_fail: bool,
}

fn reset(transport: &TransportWrapper, strappings: &[&str], reset_delay: Duration) -> Result<()> {
    log::info!("Resetting target...");
    for strapping in strappings.iter() {
        transport.pin_strapping(strapping)?.apply()?;
    }
    transport.reset_target(reset_delay, true)?;
    // We want to hold the strapping configuration here because in some life cycle states,
    // the tap multiplexing is dynamic so removing the tap strap would actually change the tap.
    Ok(())
}

const BP_TIMEOUT: Duration = Duration::from_secs(5);

fn asm_interrupt_handler(dbg: &mut ElfDebugger) -> Result<()> {
    dbg.reset(false)?;
    dbg.remove_all_breakpoints()?;

    // Attempt to trigger an exception.
    dbg.set_pc(0)?;

    dbg.run_until("_asm_exception_handler", BP_TIMEOUT)?;

    Ok(())
}

fn shutdown_execution_asm(dbg: &mut ElfDebugger) -> Result<()> {
    dbg.reset(false)?;
    dbg.remove_all_breakpoints()?;

    // Reset PC to the start of main SRAM
    dbg.set_pc(top_earlgrey::SRAM_CTRL_MAIN_RAM_BASE_ADDR as u32)?;

    // Check that the execution hits the exception handler
    dbg.run_until("_asm_exception_handler", BP_TIMEOUT)?;

    Ok(())
}

fn asm_watchdog_bark(dbg: &mut ElfDebugger) -> Result<()> {
    dbg.reset(false)?;
    dbg.remove_all_breakpoints()?;

    // Run until we check whether ROM execution is enabled
    dbg.run_until("kRomStartBootMaybeHalt", BP_TIMEOUT)?;

    // Pretend execution is enabled
    dbg.set_pc("kRomStartBootExecEn")?;

    dbg.run_until("kRomStartStoreT1ToBiteThold", BP_TIMEOUT)?;

    // Set the bite threshold to UINT32_MAX. We want to exercise that the
    // bark causes control to reach the interrupt handler.
    dbg.write_reg(RiscvGpr::T1, 0xFFFFFFFF)?;

    // Run until right after configuring the watchdog timer
    dbg.run_until("kRomStartWatchdogEnabled", BP_TIMEOUT)?;

    dbg.set_pc("kRomStartBootMaybeHalt")?;

    // Wait for the NMI handler to be hit.
    dbg.run_until("_asm_exception_handler", BP_TIMEOUT)?;

    Ok(())
}

fn asm_watchdog_bite<'t>(
    opt_dbg: &mut Option<ElfDebugger<'t>>,
    opts: &Opts,
    transport: &'t TransportWrapper,
    sym: &'t ElfSymbols,
) -> Result<()> {
    // This test requires taking the ownershup of the debugger.
    let mut dbg = opt_dbg.take().unwrap();

    dbg.reset(false)?;
    dbg.remove_all_breakpoints()?;

    // Run until we check whether ROM execution is enabled
    dbg.run_until("kRomStartBootMaybeHalt", BP_TIMEOUT)?;

    // Pretend execution is enabled
    dbg.set_pc("kRomStartBootExecEn")?;

    dbg.run_until("kRomStartStoreT1ToBiteThold", BP_TIMEOUT)?;

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

    dbg.run_until("kRomStartWatchdogEnabled", BP_TIMEOUT)?;

    dbg.set_pc("kRomStartBootMaybeHalt")?;

    // Set a breakpoint to ensure the NMI handler is not being hit.
    // If the NMI handler is hit then the PC check below will fail.
    dbg.set_breakpoint("_asm_exception_handler")?;

    // This should trigger the watchdog and cause a reset.
    // Disconnect JTAG, wait for a sufficiently long period to allow reset to complete and reconnect.
    dbg.disconnect()?;
    std::thread::sleep(BP_TIMEOUT);
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

    *opt_dbg = Some(dbg);

    Ok(())
}

fn debug_test(dbg: &mut ElfDebugger, uart: &dyn Uart) -> Result<()> {
    dbg.reset(false)?;
    dbg.remove_all_breakpoints()?;

    // Immediately after reset, we should be sitting on the Ibex reset
    // handler, the 33rd entry in the interrupt vector.
    dbg.expect_pc(SymbolicAddress::from("_rom_interrupt_vector_asm") + 32 * 4)?;

    // Executing the `j _rom_start_boot` instruction should take us
    // to _rom_start_boot.
    dbg.step()?;
    dbg.expect_pc("_rom_start_boot")?;

    // Run until we check whether ROM execution is enabled.
    dbg.run_until("kRomStartBootMaybeHalt", BP_TIMEOUT)?;

    // Pretend execution is enabled.
    dbg.set_pc("kRomStartBootExecEn")?;

    // Continue until watchdog config.
    dbg.run_until("kRomStartWatchdogEnabled", BP_TIMEOUT)?;

    // Disable watchdog config
    dbg.write_u32(
        top_earlgrey::AON_TIMER_AON_BASE_ADDR as u32
            + opentitanlib::dif::aon_timer::AonTimerReg::WdogCtrl as u32,
        0,
    )?;

    // Continue until rom_main
    dbg.run_until("rom_main", BP_TIMEOUT)?;

    // Continue until uart_init
    dbg.run_until("uart_init", BP_TIMEOUT)?;

    // Finish uart_init
    dbg.finish(BP_TIMEOUT)?;

    // Read and write GPRs
    const GPRS: &[RiscvGpr] = &[
        RiscvGpr::RA,
        RiscvGpr::SP,
        RiscvGpr::GP,
        RiscvGpr::TP,
        RiscvGpr::T0,
        RiscvGpr::T1,
        RiscvGpr::T2,
        RiscvGpr::FP,
        RiscvGpr::S1,
        RiscvGpr::A0,
        RiscvGpr::A1,
        RiscvGpr::A2,
        RiscvGpr::A3,
        RiscvGpr::A4,
        RiscvGpr::A5,
        RiscvGpr::A6,
        RiscvGpr::A7,
        RiscvGpr::S2,
        RiscvGpr::S3,
        RiscvGpr::S4,
        RiscvGpr::S5,
        RiscvGpr::S6,
        RiscvGpr::S7,
        RiscvGpr::S8,
        RiscvGpr::S9,
        RiscvGpr::S10,
        RiscvGpr::S11,
        RiscvGpr::T3,
        RiscvGpr::T4,
        RiscvGpr::T5,
        RiscvGpr::T6,
    ];

    // Test GPR reads
    let mut gpr_read = [0; 31];
    for (idx, gpr) in GPRS.iter().copied().enumerate() {
        gpr_read[idx] = dbg.read_reg(gpr)?;
    }

    // Test GPR writes
    for gpr in GPRS.iter().copied() {
        dbg.write_reg(gpr, 0x89abcdef)?;
    }

    // Restore GPRs
    for (idx, gpr) in GPRS.iter().copied().enumerate() {
        dbg.write_reg(gpr, gpr_read[idx])?;
    }

    const CSRS_TO_READ: &[RiscvCsr] = &[
        RiscvCsr::MIP,
        RiscvCsr::MHARTID,
        RiscvCsr::PMPCFG0,
        RiscvCsr::PMPCFG1,
        RiscvCsr::PMPCFG2,
        RiscvCsr::PMPCFG3,
        RiscvCsr::PMPADDR0,
        RiscvCsr::PMPADDR1,
        RiscvCsr::PMPADDR2,
        RiscvCsr::PMPADDR3,
        RiscvCsr::PMPADDR4,
        RiscvCsr::PMPADDR5,
        RiscvCsr::PMPADDR6,
        RiscvCsr::PMPADDR7,
        RiscvCsr::PMPADDR8,
        RiscvCsr::PMPADDR9,
        RiscvCsr::PMPADDR10,
        RiscvCsr::PMPADDR11,
        RiscvCsr::PMPADDR12,
        RiscvCsr::PMPADDR13,
        RiscvCsr::PMPADDR14,
        RiscvCsr::PMPADDR15,
        RiscvCsr::SCONTEXT,
        RiscvCsr::MSECCFG,
        RiscvCsr::MSECCFGH,
        RiscvCsr::TSELECT,
        RiscvCsr::DPC,
        RiscvCsr::MVENDORID,
        RiscvCsr::MARCHID,
        RiscvCsr::MIMPID,
        RiscvCsr::MHARTID,
    ];
    const CSRS_TO_WRITE: &[RiscvCsr] = &[
        RiscvCsr::MSTATUS,
        RiscvCsr::MISA,
        RiscvCsr::MIE,
        RiscvCsr::MTVEC,
        RiscvCsr::MCOUNTINHIBIT,
        RiscvCsr::MHPMEVENT3,
        RiscvCsr::MHPMEVENT4,
        RiscvCsr::MHPMEVENT5,
        RiscvCsr::MHPMEVENT6,
        RiscvCsr::MHPMEVENT7,
        RiscvCsr::MHPMEVENT8,
        RiscvCsr::MHPMEVENT9,
        RiscvCsr::MHPMEVENT10,
        RiscvCsr::MHPMEVENT11,
        RiscvCsr::MHPMEVENT12,
        RiscvCsr::MHPMEVENT13,
        RiscvCsr::MHPMEVENT14,
        RiscvCsr::MHPMEVENT15,
        RiscvCsr::MHPMEVENT16,
        RiscvCsr::MHPMEVENT17,
        RiscvCsr::MHPMEVENT18,
        RiscvCsr::MHPMEVENT19,
        RiscvCsr::MHPMEVENT20,
        RiscvCsr::MHPMEVENT21,
        RiscvCsr::MHPMEVENT22,
        RiscvCsr::MHPMEVENT23,
        RiscvCsr::MHPMEVENT24,
        RiscvCsr::MHPMEVENT25,
        RiscvCsr::MHPMEVENT26,
        RiscvCsr::MHPMEVENT27,
        RiscvCsr::MHPMEVENT28,
        RiscvCsr::MHPMEVENT29,
        RiscvCsr::MHPMEVENT30,
        RiscvCsr::MHPMEVENT31,
        RiscvCsr::MSCRATCH,
        RiscvCsr::MEPC,
        RiscvCsr::MCAUSE,
        RiscvCsr::MTVAL,
        RiscvCsr::TDATA1,
        RiscvCsr::TDATA2,
        RiscvCsr::TDATA3,
        RiscvCsr::MCONTEXT,
        RiscvCsr::MSCONTEXT,
        RiscvCsr::DCSR,
        RiscvCsr::DSCRATCH0,
        RiscvCsr::DSCRATCH1,
        RiscvCsr::MCYCLE,
        RiscvCsr::MINSTRET,
        RiscvCsr::MHPMCOUNTER3,
        RiscvCsr::MHPMCOUNTER4,
        RiscvCsr::MHPMCOUNTER5,
        RiscvCsr::MHPMCOUNTER6,
        RiscvCsr::MHPMCOUNTER7,
        RiscvCsr::MHPMCOUNTER8,
        RiscvCsr::MHPMCOUNTER9,
        RiscvCsr::MHPMCOUNTER10,
        RiscvCsr::MHPMCOUNTER11,
        RiscvCsr::MHPMCOUNTER12,
        RiscvCsr::MHPMCOUNTER13,
        RiscvCsr::MHPMCOUNTER14,
        RiscvCsr::MHPMCOUNTER15,
        RiscvCsr::MHPMCOUNTER16,
        RiscvCsr::MHPMCOUNTER17,
        RiscvCsr::MHPMCOUNTER18,
        RiscvCsr::MHPMCOUNTER19,
        RiscvCsr::MHPMCOUNTER20,
        RiscvCsr::MHPMCOUNTER21,
        RiscvCsr::MHPMCOUNTER22,
        RiscvCsr::MHPMCOUNTER23,
        RiscvCsr::MHPMCOUNTER24,
        RiscvCsr::MHPMCOUNTER25,
        RiscvCsr::MHPMCOUNTER26,
        RiscvCsr::MHPMCOUNTER27,
        RiscvCsr::MHPMCOUNTER28,
        RiscvCsr::MHPMCOUNTER29,
        RiscvCsr::MHPMCOUNTER30,
        RiscvCsr::MHPMCOUNTER31,
        RiscvCsr::MCYCLEH,
        RiscvCsr::MINSTRETH,
        RiscvCsr::MHPMCOUNTER3H,
        RiscvCsr::MHPMCOUNTER4H,
        RiscvCsr::MHPMCOUNTER5H,
        RiscvCsr::MHPMCOUNTER6H,
        RiscvCsr::MHPMCOUNTER7H,
        RiscvCsr::MHPMCOUNTER8H,
        RiscvCsr::MHPMCOUNTER9H,
        RiscvCsr::MHPMCOUNTER10H,
        RiscvCsr::MHPMCOUNTER11H,
        RiscvCsr::MHPMCOUNTER12H,
        RiscvCsr::MHPMCOUNTER13H,
        RiscvCsr::MHPMCOUNTER14H,
        RiscvCsr::MHPMCOUNTER15H,
        RiscvCsr::MHPMCOUNTER16H,
        RiscvCsr::MHPMCOUNTER17H,
        RiscvCsr::MHPMCOUNTER18H,
        RiscvCsr::MHPMCOUNTER19H,
        RiscvCsr::MHPMCOUNTER20H,
        RiscvCsr::MHPMCOUNTER21H,
        RiscvCsr::MHPMCOUNTER22H,
        RiscvCsr::MHPMCOUNTER23H,
        RiscvCsr::MHPMCOUNTER24H,
        RiscvCsr::MHPMCOUNTER25H,
        RiscvCsr::MHPMCOUNTER26H,
        RiscvCsr::MHPMCOUNTER27H,
        RiscvCsr::MHPMCOUNTER28H,
        RiscvCsr::MHPMCOUNTER29H,
        RiscvCsr::MHPMCOUNTER30H,
        RiscvCsr::MHPMCOUNTER31H,
        RiscvCsr::CPUCTRL,
        RiscvCsr::SECURESEED,
    ];

    // Test CSR reads
    for csr in CSRS_TO_READ.iter().copied() {
        dbg.read_reg(csr)?;
    }
    let mut csr_read = [0; CSRS_TO_WRITE.len()];
    for (idx, csr) in CSRS_TO_WRITE.iter().copied().enumerate() {
        csr_read[idx] = dbg.read_reg(csr)?;
    }

    // Test CSR writes
    for csr in CSRS_TO_WRITE.iter().copied() {
        dbg.write_reg(csr, 0x89abcdef)?;
    }

    // Restore CSRs
    for (idx, csr) in CSRS_TO_WRITE.iter().copied().enumerate() {
        dbg.write_reg(csr, csr_read[idx])?;
    }

    // Read and write memory (both SRAM and device)
    // See hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h
    let sram_base = top_earlgrey::SRAM_CTRL_MAIN_RAM_BASE_ADDR as u32;
    let sram_len = top_earlgrey::SRAM_CTRL_MAIN_RAM_SIZE_BYTES as u32;

    dbg.read_memory(sram_base, &mut [0; 16])?;
    dbg.read_memory(sram_base + sram_len / 2, &mut [0; 16])?;
    dbg.read_memory(sram_base + sram_len - 16, &mut [0; 16])?;

    // Manually write bytes to UART0
    let uart_base = top_earlgrey::UART0_BASE_ADDR as u32;
    let uart_wdata = opentitanlib::dif::uart::UartReg::Wdata as u32;

    dbg.write_u32(uart_base + uart_wdata, 'O' as u32)?;
    dbg.write_u32(uart_base + uart_wdata, 'K' as u32)?;
    dbg.write_u32(uart_base + uart_wdata, '!' as u32)?;

    // Execute code
    for c in "GDB-OK\r\n".bytes() {
        dbg.call("uart_putchar", &[c as u32], BP_TIMEOUT)?;
    }

    dbg.resume()?;

    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(r"OK!GDB-OK(?s:.*)BFV:0142500d")?),
        ..Default::default()
    };
    let result = console.interact(uart, None, Some(&mut std::io::stdout()))?;
    assert_eq!(result, ExitStatus::ExitSuccess);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    log::info!("Loading symbols from ELF {}", opts.elf.display());
    let sym = ElfSymbols::load_elf(&opts.elf)?;

    let uart = transport.uart("console")?;

    reset(
        &transport,
        &["PINMUX_TAP_RISCV"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    let mut jtag = opts
        .init
        .jtag_params
        .create(&transport)?
        .connect(JtagTap::RiscvTap)?;
    let result = jtag.reset(false);
    assert_eq!(result.is_err(), opts.expect_fail);
    if opts.expect_fail {
        return Ok(());
    }

    let mut dbg = Some(sym.attach(jtag));
    execute_test!(asm_interrupt_handler, dbg.as_mut().unwrap());
    execute_test!(shutdown_execution_asm, dbg.as_mut().unwrap());
    execute_test!(asm_watchdog_bark, dbg.as_mut().unwrap());
    execute_test!(asm_watchdog_bite, &mut dbg, &opts, &transport, &sym);
    execute_test!(debug_test, dbg.as_mut().unwrap(), &*uart);

    dbg.unwrap().disconnect()?;

    Ok(())
}
