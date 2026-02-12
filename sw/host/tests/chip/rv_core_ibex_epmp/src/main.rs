// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use regex::Regex;
use std::time::Duration;

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;

use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::uart::console::{ExitStatus, UartConsole};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn ibex_epmp_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset(UartRx::Clear)?;

    log::info!("Connecting to RISC-V TAP");
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    log::info!("Halting core");
    jtag.halt()?;

    // Make sure to remove any messages from the ROM.
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load SRAM program
    match opts
        .sram_program
        .load_and_execute(&mut *jtag, ExecutionMode::Jump)?
    {
        ExecutionResult::Executing => log::info!("program successfully started"),
        res => bail!("program execution failed: {:?}", res),
    }
    // Disconnect JTAG.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .remove()
        .context("failed to apply RISCV TAP strapping")?;
    jtag.disconnect()?;

    // Wait for test status pass over the UART.
    let mut console = UartConsole::new(
        Some(opts.timeout),
        Some(Regex::new(r"PASS.*\n")?),
        Some(Regex::new(r"(FAIL|FAULT).*\n")?),
    );

    let result = console.interact(&*uart, false)?;
    match result {
        ExitStatus::Timeout => Err(anyhow!("Console timeout exceeded")),
        ExitStatus::ExitSuccess => {
            log::info!(
                "ExitSuccess({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Ok(())
        }
        ExitStatus::ExitFailure => {
            log::info!(
                "ExitFailure({:?})",
                console.captures(result).unwrap().get(0).unwrap().as_str()
            );
            Err(anyhow!("Matched exit_failure expression"))
        }
    }
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(ibex_epmp_test, &opts, &transport);

    Ok(())
}
