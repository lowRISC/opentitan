// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::debug::dmi::{DmiDebugger, OpenOcdDmi};
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,
}

// Needs to match util/openocd/target
const RISCV_IDCODE: u32 = 0x10001cdf;

#[allow(clippy::unusual_byte_groupings)]
fn test_dtm(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let mut hart = dmi.select_hart(0)?;

    let hartinfo = hart.hartinfo()?;
    log::info!("Hartinfo: {:#x}", hartinfo);
    // Two dscratch registers, memory-mapped, two data registers, offset at 0x380.
    assert_eq!(hartinfo, 0x2_1_2_380);

    // Write to data0 and data1 and readback.
    let rand0: u32 = rand::random();
    let rand1: u32 = rand::random();
    dmi.set_data(0, rand0)?;
    dmi.set_data(1, rand1)?;

    assert_eq!(dmi.data(0)?, rand0);
    assert_eq!(dmi.data(1)?, rand1);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_dtm, &opts, &transport);

    Ok(())
}
