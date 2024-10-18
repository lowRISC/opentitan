// Copyright lowRISC contributors (OpenTitan project).
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

    // For test_unlocked* and RMA state, test that we can switch TAP without reset.
    let (needs_reset, rv_dm_enabled) = match lc_state {
        DifLcCtrlState::TestUnlocked0
        | DifLcCtrlState::TestUnlocked1
        | DifLcCtrlState::TestUnlocked2
        | DifLcCtrlState::TestUnlocked3
        | DifLcCtrlState::TestUnlocked4
        | DifLcCtrlState::TestUnlocked5
        | DifLcCtrlState::TestUnlocked6
        | DifLcCtrlState::TestUnlocked7
        | DifLcCtrlState::Rma => (false, true),
        DifLcCtrlState::Dev => (true, true),
        _ => (true, false),
    };

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    // Test RISC-V TAP
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    if needs_reset {
        transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    }

    let jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap);

    assert_eq!(rv_dm_enabled, jtag.is_ok());

    if let Ok(mut jtag) = jtag {
        let mut lc_state_rv = 0;
        jtag.read_memory32(
            top_earlgrey::LC_CTRL_REGS_BASE_ADDR as u32 + LcCtrlReg::LcState as u32,
            core::slice::from_mut(&mut lc_state_rv),
        )?;
        let lc_state_rv = DifLcCtrlState::from_redundant_encoding(lc_state_rv)?;
        assert_eq!(lc_state, lc_state_rv);
        jtag.disconnect()?;
    }

    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    // Test DFT TAP
    transport.pin_strapping("PINMUX_TAP_DFT")?.apply()?;
    if needs_reset {
        transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    }

    // If RV-DM is disabled, strapping DFT tap will result in LC TAP being selected.
    if !rv_dm_enabled {
        opts.init
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?
            .disconnect()?;
    } else {
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

        // For everything other than test_unlocked* and RMA states, the DFT TAP should not exist.
        let expected_idcode = if needs_reset { opts.dft_idcode } else { None };
        assert_eq!(idcode, expected_idcode);
        openocd.shutdown()?;
    }

    transport.pin_strapping("PINMUX_TAP_DFT")?.remove()?;
    if needs_reset {
        transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    }

    // Now check that there's no JTAG TAP present.
    let mut openocd = opts.init.jtag_params.create(transport)?.into_raw()?;
    // Perform JTAG initialisation and capture the result.
    let init_result = openocd.execute("capture \"jtag init\"")?;
    assert!(init_result.contains("JTAG scan chain interrogation failed"));
    openocd.shutdown()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(test_jtag_tap_sel, &opts, &transport);

    Ok(())
}
