// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(flatten)]
    jtag_params: JtagParams,

    #[structopt(
        long, parse(try_from_str = DifLcCtrlState::parse_lc_state_str),
        default_value = "test_unlocked0",
        help = "LC state to expect the chip to be initialized in."
    )]
    initial_lc_state: DifLcCtrlState,
}

fn manuf_scrap(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the chip, select the LC TAP, and connect to it.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let jtag = transport.jtag(&opts.jtag_params)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check the initial LC state.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        opts.initial_lc_state.redundant_encoding(),
        "Invalid initial LC state.",
    );

    trigger_lc_transition(
        transport,
        jtag.clone(),
        DifLcCtrlState::Scrap,
        /*use_external_clk=*/ false,
        opts.init.bootstrap.options.reset_delay,
    )?;

    // Check the LC state is SCRAP.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::Scrap.redundant_encoding(),
    );

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(manuf_scrap, &opts, &transport);

    Ok(())
}
