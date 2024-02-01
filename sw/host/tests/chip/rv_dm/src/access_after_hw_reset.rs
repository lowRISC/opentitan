// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::mem::MemWriteReq;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Path to the ELF file being tested on the device.
    #[arg(long)]
    firmware_elf: PathBuf,
}

fn test_access_after_hw_reset(
    opts: &Opts,
    transport: &TransportWrapper,
    reset_addr: u32,
) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Enable console and wait for the message.
    let uart = &*transport.uart("console")?;
    uart.set_flow_control(true)?;
    UartConsole::wait_for(uart, r"Running [^\r\n]*", opts.timeout)?;
    UartConsole::wait_for(uart, r"Waiting for commands", opts.timeout)?;

    // Check debugger is available.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    assert_eq!(
        jtag.as_raw()?.execute("$_TARGETNAME.0 curstate")?,
        "running"
    );
    jtag.disconnect()?;

    MemWriteReq::execute(uart, reset_addr, &[1])?;
    UartConsole::wait_for(uart, r"Reset complete", opts.timeout)?;

    // Check debugger is available.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    assert_eq!(
        jtag.as_raw()?.execute("$_TARGETNAME.0 curstate")?,
        "running"
    );
    jtag.disconnect()?;

    UartConsole::wait_for(uart, r"PASS!", opts.timeout)?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let elf_file = std::fs::read(&opts.firmware_elf).context("failed to read ELF")?;
    let object = object::File::parse(elf_file.as_ref()).context("failed to parse ELF")?;
    let reset_addr = test_utils::object::symbol_addr(&object, "kReset")?;

    let transport = opts.init.init_target()?;
    execute_test!(test_access_after_hw_reset, &opts, &transport, reset_addr);

    Ok(())
}
