// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use clap::Parser;
use once_cell::sync::Lazy;
use regex::Regex;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::util::parse_int::ParseInt;

use top_earlgrey::top_earlgrey;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// IDCODE of the DFT TAP. If not specified, the test will check that DFT does not exist.
    #[arg(long, value_parser = u32::from_str)]
    dft_idcode: Option<u32>,
}

fn test_jtag_tap_sel(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Avoid watchdog timeout by entering bootstrap mode.
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;

    // Test the LC TAP
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;
    let lc_state =
        DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    // Test RISC-V TAP
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;
    let mut lc_state_rv = 0;
    jtag.read_memory32(
        top_earlgrey::LC_CTRL_BASE_ADDR as u32 + LcCtrlReg::LcState as u32,
        core::slice::from_mut(&mut lc_state_rv),
    )?;
    let lc_state_rv = DifLcCtrlState::from_redundant_encoding(lc_state_rv)?;
    assert_eq!(lc_state, lc_state_rv);

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    // Test DFT TAP
    transport.pin_strapping("PINMUX_TAP_DFT")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // For DFT test we need to do raw OpenOCD command.
    let mut openocd = opts.init.jtag_params.create(transport)?.into_raw()?;
    // Perform JTAG initialisation and capture the result.
    let init_result = openocd.execute("capture \"jtag init\"")?;

    static ID_REGEX: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"tap/device found: 0x([0-9A-Fa-f]+) \(").unwrap());
    let idcode = if init_result.contains("JTAG scan chain interrogation failed") {
        None
    } else {
        Some(u32::from_str_radix(
            ID_REGEX
                .captures(&init_result)
                .context("Failed to parse IDCODE from OpenOCD output")?
                .get(1)
                .unwrap()
                .as_str(),
            16,
        )?)
    };
    assert_eq!(idcode, opts.dft_idcode);

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_jtag_tap_sel, &opts, &transport);

    Ok(())
}
