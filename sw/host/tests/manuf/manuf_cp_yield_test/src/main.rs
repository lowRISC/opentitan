// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This test checks that we can change TAP strapping from CPU to the LC_CTRL
//! and still use the interface without resetting.
//!
//! Both interfaces are used to check they're accessible. This is only possible
//! in some lifecycle states: `TEST_UNLOCKED0` is used in this case.

use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg, LcCtrlStatus};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::extclk::{ClockSpeed, ExternalClock};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::wait_for_status;
use top_earlgrey::top_earlgrey;

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

fn manuf_cp_yield_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the chip, select the CPU TAP, and connect to it.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)
        .context("failed to connect to RISCV TAP over JTAG")?;

    ExternalClock::enable(&mut *jtag, ClockSpeed::High)
        .context("failed to enable external clock")?;

    // Read and write memory to verify connection.

    // Check we can read the MMIO system memory region by reading the LC state.
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(
        &mut *jtag,
        Duration::from_secs(3),
        LcCtrlStatus::INITIALIZED,
    )?;
    let mut encoded_lc_state = [0u32];
    jtag.read_memory32(
        top_earlgrey::LC_CTRL_BASE_ADDR as u32 + LcCtrlReg::LcState as u32,
        &mut encoded_lc_state,
    )?;
    assert_eq!(
        encoded_lc_state[0],
        opts.initial_lc_state.redundant_encoding()
    );

    // Without resetting, change TAP strapping to the LC and reconnect.
    jtag.disconnect().context("failed to disconnect JTAG")?;
    transport
        .pin_strapping("PINMUX_TAP_LC")?
        .apply()
        .context("failed to apply LC TAP strapping")?;
    jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)
        .context("failed to connect to LC TAP over JTAG")?;

    // Read and write LC state register to verify connection.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, opts.initial_lc_state.redundant_encoding());

    jtag.disconnect().context("failed to disconnect JTAG")?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(manuf_cp_yield_test, &opts, &transport);

    Ok(())
}
