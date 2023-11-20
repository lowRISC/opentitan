// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long)]
    expect_fail: bool,
}

fn access_jtag(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Avoid watchdog timeout by entering bootstrap mode.
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;

    // Reset into RV_DM for testing.
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let jtag_result = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap);

    if opts.expect_fail {
        assert!(
            jtag_result.is_err(),
            "JTAG access to RV_DM established, but access is not allowed"
        );
        return Ok(());
    }

    let mut openocd = jtag_result?.into_raw()?;

    // Test that we can write sbaddress0 (address 0x39) register over DMI
    let random_value: u32 = rand::random();
    log::info!("Writing {random_value:#x} to sbaddress0");
    openocd.execute(&format!("riscv dmi_write 0x39 {random_value:#x}"))?;
    let readback = u32::from_str_radix(
        openocd
            .execute("riscv dmi_read 0x39")?
            .trim()
            .trim_start_matches("0x"),
        16,
    )?;
    assert_eq!(random_value, readback);

    openocd.shutdown()?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(access_jtag, &opts, &transport);

    Ok(())
}
