// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use clap::Parser;
use regex::Regex;

use opentitanlib::app::TransportWrapper;
use opentitanlib::debug::elf_debugger::{ElfSymbols, SymbolicAddress};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagTap, RiscvCsr, RiscvGpr};
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

    /// Breakpoint timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "5s")]
    breakpoint_timeout: Duration,
}

fn debug_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    log::info!("Loading symbols from ELF {}", opts.elf.display());
    let sym = ElfSymbols::load_elf(&opts.elf)?;

    // This test requires RV_DM access so first strap and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let uart = transport.uart("console")?;

    let jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap);

    if opts.expect_fail {
        assert!(jtag.is_err());
        return Ok(());
    }

    let mut dbg = sym.attach(jtag?);
    dbg.reset(false)?;

    // Immediately after reset, we should be sitting on the Ibex reset
    // handler, the 33rd entry in the interrupt vector.
    dbg.expect_pc(SymbolicAddress::from("_rom_interrupt_vector_asm") + 32 * 4)?;

    // Executing the `j _rom_start_boot` instruction should take us
    // to _rom_start_boot.
    dbg.step()?;
    dbg.expect_pc("_rom_start_boot")?;

    // Run until we check whether ROM execution is enabled.
    dbg.run_until("kRomStartBootMaybeHalt", opts.breakpoint_timeout)?;

    // Pretend execution is enabled.
    dbg.set_pc("kRomStartBootExecEn")?;

    // Continue until watchdog config.
    dbg.run_until("kRomStartWatchdogEnabled", opts.breakpoint_timeout)?;

    // Disable watchdog config
    dbg.write_u32(
        top_earlgrey::AON_TIMER_AON_BASE_ADDR as u32
            + opentitanlib::dif::aon_timer::AonTimerReg::WdogCtrl as u32,
        0,
    )?;

    // Continue until rom_main
    dbg.run_until("rom_main", opts.breakpoint_timeout)?;

    // Continue until uart_init
    dbg.run_until("uart_init", opts.breakpoint_timeout)?;

    // Finish uart_init
    dbg.finish(opts.breakpoint_timeout)?;

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
        // `uart_write_imm` takes a uint64_t as an argument.
        dbg.call("uart_write_imm", &[c as u32, 0u32], opts.breakpoint_timeout)?;
    }

    dbg.resume()?;

    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);
    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(r"OK!GDB-OK(?s:.*)BFV:0142500d")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    assert_eq!(result, ExitStatus::ExitSuccess);

    dbg.disconnect()?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(debug_test, &opts, &transport);

    Ok(())
}
