// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This is the test harness for the `sram_ctrl_lc_escalation` test which
//! checks that SRAMs can no longer be accessed after an alert is escalated.
//!
//! We have to check SRAM access over the debugger and not from within Ibex
//! because the core also locks up on escalation.

use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{ensure, Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{Jtag, JtagTap};
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::{MemRead32Req, MemWriteReq};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Path to the ELF file being tested on the device.
    #[arg(long)]
    firmware_elf: PathBuf,
}

/// Addresses of symbols in the ELF file that we will access.
///
/// Note that the `main` and `ret` addresses point to variables holding the
/// main and retention SRAM addresses and not those addresses directly.
#[derive(Debug, Clone, Copy)]
struct Addresses {
    test_phase: u32,
    main: u32,
    ret: u32,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_file = fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;

    let addresses = Addresses {
        test_phase: test_utils::object::symbol_addr(&object, "test_phase")?,
        main: test_utils::object::symbol_addr(&object, "sram_buffer_addr_main")?,
        ret: test_utils::object::symbol_addr(&object, "sram_buffer_addr_ret")?,
    };

    let transport = opts.init.init_target()?;
    let uart_console = transport.uart("console")?;

    execute_test!(lc_escalation, &opts, &transport, &*uart_console, addresses);

    Ok(())
}

/// Send and receive data with a device's UART.
fn lc_escalation(
    opts: &Opts,
    transport: &TransportWrapper,
    console: &dyn Uart,
    addresses: Addresses,
) -> Result<()> {
    UartConsole::wait_for(console, r"waiting for commands", opts.timeout)?;

    // Get the addresses of main and retention SRAM that we can access.
    let main_addr = MemRead32Req::execute(console, addresses.main)?;
    let ret_addr = MemRead32Req::execute(console, addresses.ret)?;

    // Enable JTAG debugging.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    // Test that we can write to and read back the SRAMs over the debugger.
    write_read(&mut *jtag, main_addr, 0xaaaa_aaaa)?;
    write_read(&mut *jtag, ret_addr, 0xbbbb_bbbb)?;

    // Let the device side of the test escalate an alert and lock up.
    MemWriteReq::execute(console, addresses.test_phase, &[1])?;

    log::info!("-------------------------------");
    log::info!("EXPECTING JTAG ACCESSES TO FAIL");
    log::info!("-------------------------------");

    // Check that we can no longer access the SRAMs after escalation.
    // These operations should time out.
    ensure!(
        write_read(&mut *jtag, main_addr, 0xcccc_cccc).is_err(),
        "expected main SRAM access to fail"
    );
    ensure!(
        write_read(&mut *jtag, ret_addr, 0xdddd_dddd).is_err(),
        "expected retention SRAM access to fail"
    );

    // Reset the chip and try again - the SRAMs should now be unlocked.
    jtag.disconnect()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    log::info!("----------------------------------");
    log::info!("EXPECTING JTAG ACCESSES TO SUCCEED");
    log::info!("----------------------------------");

    write_read(&mut *jtag, main_addr, 0xeeee_eeee)?;
    write_read(&mut *jtag, ret_addr, 0xffff_ffff)?;

    Ok(())
}

// Write to and read back a word from the given address over the debugger.
fn write_read(jtag: &mut dyn Jtag, addr: u32, data: u32) -> Result<()> {
    let mut buf = 0;
    jtag.write_memory32(addr, &[data])?;
    jtag.read_memory32(addr, std::slice::from_mut(&mut buf))?;

    assert_eq!(buf, data);
    Ok(())
}
