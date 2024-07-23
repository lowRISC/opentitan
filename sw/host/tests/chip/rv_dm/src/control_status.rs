// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::debug::dmi::{consts, DmiDebugger, OpenOcdDmi};
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,
}

// Needs to match util/openocd/target
const RISCV_IDCODE: u32 = 0x10001cdf;

fn test_control_status(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let mut openocd = opts.init.jtag_params.create(transport)?.into_raw()?;

    // Configure OpenOCD to expect RISC-V tap and initialize JTAG.
    assert_eq!(
        openocd.execute(&format!(
            "jtag newtap riscv tap -irlen 5 -expected-id {RISCV_IDCODE:#x}"
        ))?,
        ""
    );
    assert_eq!(openocd.execute("init")?, "");

    let mut dmi = DmiDebugger::new(OpenOcdDmi::new(openocd, "riscv.tap")?);

    // Check dmstatus indicates havereset for Ibex (power-on reset) and set ackhavereset to clear it.
    let mut hart = dmi.select_hart(0)?;
    let dmstatus = hart.dmstatus()?;
    assert!(dmstatus & consts::DMSTATUS_ANYHAVERESET_MASK != 0);
    hart.set_dmcontrol(consts::DMCONTROL_ACKHAVERESET_MASK)?;

    // Write all 1s to hartsel and confirm readback.
    let hartsel_mask = dmi.hartsel_mask()?;
    // Since this target only supports 1 hart, no hartsel bits could be set.
    assert_eq!(hartsel_mask, 0);

    let mut hart = dmi.select_hart(0)?;
    assert!(hart.state()?.running);

    hart.set_halt_request(true)?;
    hart.wait_halt()?;
    hart.set_halt_request(false)?;

    hart.set_resume_request(true)?;
    hart.wait_resume()?;
    hart.set_resume_request(false)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_control_status, &opts, &transport);

    Ok(())
}
