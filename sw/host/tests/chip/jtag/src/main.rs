// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use regex::Regex;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boolean::MultiBitBool8;
use opentitanlib::dif::lc_ctrl::LcCtrlReg;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
    #[structopt(flatten)]
    jtag: JtagParams,
}

fn reset(transport: &TransportWrapper, strappings: &[&str], reset_delay: Duration) -> Result<()> {
    log::info!("Resetting target...");
    for strapping in strappings.iter() {
        transport.apply_pin_strapping(strapping)?;
    }
    transport.reset_target(reset_delay, true)?;
    // we want to hold the strapping configuration here because in some life cycle states,
    // the tap multiplexing is dynamic so remove the tap strap would actually change the tap
    Ok(())
}

fn test_openocd(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the device and confirm that its lifecycle state is now RMA by
    // reading the "LCV:" line from the UART.
    let uart = transport.uart("console")?;

    reset(transport, &[], opts.init.bootstrap.options.reset_delay)?;
    const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);

    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(Regex::new(r"PASS!")?),
        ..Default::default()
    };
    let result = console.interact(&*uart, None, Some(&mut std::io::stdout()))?;
    log::info!("result: {:?}", result);

    reset(
        transport,
        &["PINMUX_TAP_LC"],
        opts.init.bootstrap.options.reset_delay,
    )?;

    let jtag = transport.jtag(&opts.jtag)?;
    jtag.connect(JtagTap::LcTap)?;

    // Test reads by checking the LC_STATE register
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?, 0x2739ce73);

    // Test writes by trying to claim the transitions mutex
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0x00);
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::True) as u32,
    )?;
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0x01);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_openocd, &opts, &transport);

    Ok(())
}
