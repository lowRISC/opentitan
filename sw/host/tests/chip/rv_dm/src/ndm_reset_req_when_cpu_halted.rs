// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagTap, RiscvCsr};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::poll::poll_until;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

const DCSR_CAUSE_SHIFT: u32 = 6;
const DCSR_CAUSE_MASK: u32 = 0x7 << DCSR_CAUSE_SHIFT;
const DCSR_CAUSE_HALTREQ: u32 = 0x3 << DCSR_CAUSE_SHIFT;

fn test_ndm_reset_req_when_halted(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // This test requires RV_DM access so first strap and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Enable console and wait for the message.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    log::info!("Waiting for \"Ready for CPU halt request\" message");
    let _ = UartConsole::wait_for(&*uart, "Ready for CPU halt request", opts.timeout)?;

    // Connect via JTAG.
    // We need to obtain raw OpenOCD instance for direct DMI manipulation.
    // Debug module will be activated by OpenOCD.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    // Verify the CPU is running before asserting haltreq.
    assert_eq!(
        jtag.as_raw()?.execute("$_TARGETNAME.0 curstate")?,
        "running"
    );

    // Initiate a CPU halt request and wait CPU to be halted.
    jtag.halt()?;
    assert_eq!(jtag.as_raw()?.execute("$_TARGETNAME.0 curstate")?, "halted");

    // Read DCSR and verify the cause field.
    let dcsr = jtag.read_riscv_reg(&RiscvCsr::DCSR.into())?;
    assert_eq!(
        dcsr & DCSR_CAUSE_MASK,
        DCSR_CAUSE_HALTREQ,
        "DCSR cause should be haltreq"
    );

    jtag.reset(true)?;

    poll_until(opts.timeout, Duration::from_millis(10), || {
        Ok(jtag.as_raw()?.execute("$_TARGETNAME.0 curstate")? == "running")
    })?;

    // Let the CPU SW run its course (second reset phase after NDM reset).
    UartConsole::wait_for(&*uart, r"PASS!", opts.timeout)?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_ndm_reset_req_when_halted, &opts, &transport);

    Ok(())
}
