// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// LC state to expect the chip to be initialized in.
    #[arg(
        long,
        value_parser = DifLcCtrlState::parse_lc_state_str,
        default_value = "test_unlocked0"
    )]
    initial_lc_state: DifLcCtrlState,
}

fn manuf_scrap(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the chip, select the LC TAP, and connect to it.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check the initial LC state.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        opts.initial_lc_state.redundant_encoding(),
        "Invalid initial LC state.",
    );

    // CPU execution is disabled in the SCRAP state so we can safely reconnect
    // to the LC TAP after the transition without risking the chip resetting.
    trigger_lc_transition(
        transport,
        &mut *jtag,
        DifLcCtrlState::Scrap,
        None,
        /*use_external_clk=*/ false,
        opts.init.bootstrap.options.reset_delay,
        Some(JtagTap::LcTap),
    )?;

    // Check the LC state is SCRAP.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::Scrap.redundant_encoding(),
    );

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(manuf_scrap, &opts, &transport);

    Ok(())
}
