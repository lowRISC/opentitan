// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::debug::dmi::{consts, DmiDebugger, OpenOcdDmi};
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

// Needs to match util/openocd/target
const RISCV_IDCODE: u32 = 0x10001cdf;

fn test_ndm_reset_req(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // This test requires RV_DM access so first strap and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Enable console and wait for the message.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Connect via JTAG and trigger a NDM reset
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        // .connect(JtagTap::RiscvTap)?;
        .into_raw()?;

    // Configure OpenOCD to expect RISC-V tap and initialize JTAG.
    assert_eq!(
        jtag.execute(&format!(
            "jtag newtap riscv tap -irlen 5 -expected-id {RISCV_IDCODE:#x}"
        ))?,
        ""
    );
    assert_eq!(jtag.execute("init")?, "");

    let mut dmi = DmiDebugger::new(OpenOcdDmi::new(jtag, "riscv.tap")?);

    // Check dmstatus indicates havereset for Ibex (power-on reset) and set ackhavereset to clear it.
    let mut hart = dmi.select_hart(0)?;
    let dmstatus = hart.dmstatus()?;
    assert!(dmstatus & consts::DMSTATUS_ANYHAVERESET_MASK != 0);
    assert!(dmstatus & consts::DMSTATUS_ALLHAVERESET_MASK != 0);
    hart.set_dmcontrol(consts::DMCONTROL_ACKHAVERESET_MASK)?;

    // Check that anyhavereset is now low.
    let dmstatus = hart.dmstatus()?;
    assert!(dmstatus & consts::DMSTATUS_ANYHAVERESET_MASK == 0);
    assert!(dmstatus & consts::DMSTATUS_ALLHAVERESET_MASK == 0);

    log::info!("Waiting for \"wait for ndm reset\" message");
    let _ = UartConsole::wait_for(&*uart, "wait for ndm reset", opts.timeout)?;

    log::info!("Issuing an NDM reset request");
    hart.set_dmcontrol(consts::DMCONTROL_NDMRESET_MASK)?;

    // Read anyhavereset to ensure that it stays low.
    let dmstatus = hart.dmstatus()?;
    assert!(dmstatus & consts::DMSTATUS_ANYHAVERESET_MASK == 0);
    assert!(dmstatus & consts::DMSTATUS_ALLHAVERESET_MASK == 0);

    log::info!("Clearing NDM reset request");
    hart.set_dmcontrol(0)?;

    // Read anyhavereset again, it now should have been set.
    // Note that there is a brief period of time between clearing ndmreset and anyhavereset going high, but
    // JTAG speed is too slow compared to system reset and we cannot observe it.
    let dmstatus = hart.dmstatus()?;
    assert!(dmstatus & consts::DMSTATUS_ANYHAVERESET_MASK != 0);
    assert!(dmstatus & consts::DMSTATUS_ALLHAVERESET_MASK != 0);

    UartConsole::wait_for(&*uart, r"PASS!", opts.timeout)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_ndm_reset_req, &opts, &transport);

    Ok(())
}
