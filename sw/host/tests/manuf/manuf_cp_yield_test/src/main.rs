// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This test checks that we can change TAP strapping from CPU to the LC_CTRL
//! and still use the interface without resetting.
//!
//! Both interfaces are used to check they're accessible. This is only possible
//! in some lifecycle states: `TEST_UNLOCKED0` is used in this case.

use anyhow::Context;
use structopt::StructOpt;

use opentitanlib::chip::boolean::MultiBitBool4;
use opentitanlib::dif::clkmgr::{ClkmgrExtclkCtrl, ClkmgrReg};
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use top_earlgrey::top_earlgrey_memory;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
    #[structopt(flatten)]
    jtag: JtagParams,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::from_args();
    opts.init.init_target()?;

    let transport = opts.init.init_target()?;

    // Begin with the TAP straps set for the CPU.
    transport
        .pin_strapping("PINMUX_TAP_RISCV")?
        .apply()
        .context("failed to apply RISCV TAP strapping")?;
    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset")?;

    let jtag = transport.jtag(&opts.jtag)?;

    // Connect to the CPU over JTAG.
    jtag.connect(JtagTap::RiscvTap)
        .context("failed to connect to RISCV TAP over JTAG")?;

    // Enable the external clock through JTAG.

    let clkmgr_base_addr = top_earlgrey_memory::TOP_EARLGREY_CLKMGR_AON_BASE_ADDR as u32;

    // Enable writing to the external clock register.
    let extclk_ctrl_regwen_addr = clkmgr_base_addr + ClkmgrReg::ExtclkCtrlRegwen as u32;
    jtag.write_memory32(extclk_ctrl_regwen_addr, &[1])
        .context("failed to set EXTCLK_CTRL_REGWEN")?;

    // Enable the external clock.
    let extclk_ctrl_addr = clkmgr_base_addr + ClkmgrReg::ExtclkCtrl as u32;
    let extclk_enable = ClkmgrExtclkCtrl::SEL.emplace(u8::from(MultiBitBool4::True) as u32);
    jtag.write_memory32(extclk_ctrl_addr, &[extclk_enable])
        .context("failed to set EXTCLK_CTRL_SET bitfield")?;

    // Read and write memory to verify connection.

    // Check the lifecycle state via its memory map.
    let mut reset_info_buf = [0];
    jtag.read_memory32(
        top_earlgrey_memory::TOP_EARLGREY_LC_CTRL_BASE_ADDR as u32 + LcCtrlReg::LcState as u32,
        &mut reset_info_buf,
    )?;

    assert_eq!(
        reset_info_buf[0],
        DifLcCtrlState::TestUnlocked0.redundant_encoding()
    );

    // Without resetting, changing TAP strapping to the LC and reconnect JTAG.

    jtag.disconnect().context("failed to disconnect JTAG")?;

    transport
        .pin_strapping("PINMUX_TAP_LC")?
        .apply()
        .context("failed to apply LC TAP strapping")?;

    jtag.connect(JtagTap::LcTap)
        .context("failed to connect to LC TAP over JTAG")?;

    // Read and write registers to verify connection.

    // Check the LC state is `TEST_UNLOCKED0`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked0.redundant_encoding());

    jtag.disconnect().context("failed to disconnect JTAG")?;

    Ok(())
}
