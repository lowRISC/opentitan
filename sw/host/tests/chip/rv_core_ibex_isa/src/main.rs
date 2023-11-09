// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::{bail, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagTap, RiscvReg, RiscvGpr};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};

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

fn ibex_isa_smoke_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

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
        .load_and_execute(&mut *jtag, ExecutionMode::JumpAndWait(Duration::from_secs(5)))?
    {
        ExecutionResult::ExecutionDone => log::info!("program successfully ran"),
        res => bail!("program execution failed: {:?}", res),
    }
    let a0 = jtag.read_riscv_reg(&RiscvReg::Gpr(RiscvGpr::A0))?;
    log::info!("Return Value (a0): {a0}");
    // Disconnect JTAG.
    jtag.halt()?;
    jtag.disconnect()?;

    assert_eq!(a0, 0, "An instruction failed");

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(ibex_isa_smoke_test, &opts, &transport);

    Ok(())
}
