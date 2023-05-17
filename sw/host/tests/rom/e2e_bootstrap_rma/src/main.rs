// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Bootstrap RMA e2e test.
//! This test harness:
//!
//! 1. Checks that the ROM times out and resets under the `RMA_BOOTSTRAP` strapping.
//! 2. Triggers a LC transition from `PROD` to `RMA` and checks for success.

use std::io;
use std::iter;
use std::time::Duration;

use anyhow::{bail, Context};
use regex::Regex;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::chip::boolean::MultiBitBool8;
use opentitanlib::dif::lc_ctrl::{
    DifLcCtrlState, DifLcCtrlToken, LcCtrlReg, LcCtrlStatus, LcCtrlTransitionCmd,
    LcCtrlTransitionRegwen,
};
use opentitanlib::dif::rstmgr::DifRstmgrResetInfo;
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition;
use opentitanlib::uart::console::{ExitStatus, UartConsole};

/// Timeout for waiting for data over the console.
const CONSOLE_TIMEOUT: Duration = Duration::from_secs(5);

/// CLI args for this test.
#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,
}

fn main() -> anyhow::Result<()> {
    let opts = Opts::from_args();

    opts.init.init_logging();

    let transport = opts
        .init
        .init_target()
        .context("failed to initialise target")?;

    execute_test!(test_no_rma_command, &opts, &transport);
    execute_test!(test_rma_command, &opts, &transport);

    Ok(())
}

/// Iteration 1 of the `rom_bootstrap_rma` testpoint.
///
/// Verifies that the ROM times out on spin cycles, automatically resets the
/// device, and logs the expected reset reasons. Does not issue the life cycle
/// RMA command.
fn test_no_rma_command(opts: &Opts, transport: &TransportWrapper) -> anyhow::Result<()> {
    let uart = transport.uart("console").context("failed to get UART")?;

    let rma_bootstrap_strapping = transport.pin_strapping("RMA_BOOTSTRAP")?;

    rma_bootstrap_strapping
        .apply()
        .context("failed to apply RMA_BOOTSTRAP strapping")?;

    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset target")?;

    // Remove the RMA_BOOTSTRAP strapping to bring the device out of the RMA spin loop.
    rma_bootstrap_strapping
        .remove()
        .context("failed to remove strapping RMA_BOOTSTRAP")?;

    log::info!("Waiting for reset reasons over the console...");

    // Strings expected from the console representing success or failure.
    let expected_bitfield = u32::from(DifRstmgrResetInfo::Por) | u32::from(DifRstmgrResetInfo::Sw);
    let exit_success =
        Regex::new(format!("reset_info_bitfield: 0x{expected_bitfield:x}\r\n").as_str())
            .context("failed to build regex")?;
    let exit_failure =
        Regex::new("reset_info_bitfield: 0x[0-9a-f]+\r\n").context("failed to build regex")?;

    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(exit_success),
        exit_failure: Some(exit_failure),
        ..Default::default()
    };

    let mut stdout = io::stdout();
    let result = console
        .interact(&*uart, None, Some(&mut stdout))
        .context("failed to interact with console")?;

    match result {
        ExitStatus::ExitSuccess => Ok(()),
        result => bail!("FAIL: {result:?}"),
    }
}

/// Iteration 2 of the `rom_bootstrap_rma` testpoint.
///
/// Issues the lifecycle RMA command and ensures the RMA transition is completed
/// successfully.
fn test_rma_command(opts: &Opts, transport: &TransportWrapper) -> anyhow::Result<()> {
    let rma_bootstrap_strapping = transport.pin_strapping("RMA_BOOTSTRAP")?;
    let tap_strapping = transport.pin_strapping("PINMUX_TAP_LC")?;

    // Need to reset with `RMA_BOOTSTRAP` set.
    rma_bootstrap_strapping
        .apply()
        .context("failed to apply RMA_BOOTSTRAP strapping")?;

    // We keep `PINMUX_TAP_LC` set so that resets due to transition don't
    // disconnect us from the LC TAP.
    tap_strapping
        .apply()
        .context("failed to apply PINMUX_TAP_LC strapping")?;

    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset target")?;

    log::info!("Connecting to JTAG interface");

    let jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)
        .context("failed to connect to JTAG")?;

    // Wait for the lifecycle controller to enter the `READY` state from
    // which it accepts transition commands.
    lc_transition::wait_for_status(&jtag, Duration::from_secs(3), LcCtrlStatus::READY)
        .context("failed to wait for lifecycle controller to be ready")?;

    // Check we're in the `PROD` state with 5 transitions registered.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::Prod.redundant_encoding()
    );
    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcTransitionCnt)?, 5);

    // Attempt to claim the transition mutex.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::True) as u32,
    )?;
    // Will be true if the transition was successful.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::ClaimTransitionIf)?,
        u8::from(MultiBitBool8::True) as u32
    );
    // And hardware will enable writing to transition registers.
    let regwen = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?;
    let regwen = LcCtrlTransitionRegwen::from_bits(regwen)
        .context("TRANSITION_REGWEN has invalid bits set")?;
    assert_eq!(regwen, LcCtrlTransitionRegwen::TRANSITION_REGWEN);

    // Multi-reg registers for the transition token.
    let token_regs = [
        &LcCtrlReg::TransitionToken0,
        &LcCtrlReg::TransitionToken1,
        &LcCtrlReg::TransitionToken2,
        &LcCtrlReg::TransitionToken3,
    ];
    // This is the preimage of the RMA token, randomly generated. The postimage
    // is was generated using the `gen_rma_token.py` script and embedded in the
    // OTP's SECRET2 partition.
    let token = DifLcCtrlToken::from([
        0x53, 0xa3, 0x81, 0x2b, 0x5a, 0x4c, 0x04, 0xa4, //
        0x85, 0xda, 0xac, 0x25, 0x2d, 0x14, 0x5c, 0xaf,
    ]);
    let token_words = token.into_register_values();

    // Write token to the multi-register.
    for (reg, value) in iter::zip(token_regs, token_words) {
        jtag.write_lc_ctrl_reg(reg, value)?;
    }

    // Read back the values to confirm the write.
    for (reg, value) in iter::zip(token_regs, token_words) {
        assert_eq!(jtag.read_lc_ctrl_reg(reg)?, value);
    }

    // Set the transition target to `RMA` and read back to confirm.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::TransitionTarget,
        DifLcCtrlState::Rma.redundant_encoding(),
    )?;
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionTarget)?,
        DifLcCtrlState::Rma.redundant_encoding(),
    );

    log::info!("Initiating lifecycle transition");

    // Write `START` to the `TRANSITION_CMD` register.
    jtag.write_lc_ctrl_reg(&LcCtrlReg::TransitionCmd, LcCtrlTransitionCmd::START.bits())?;

    assert_eq!(jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionRegwen)?, 0);

    let status = jtag.read_lc_ctrl_reg(&LcCtrlReg::Status)?;
    let status = LcCtrlStatus::from_bits(status).context("invalid status bits")?;
    assert_eq!(status, LcCtrlStatus::INITIALIZED);

    // Poll until status register reports a successful transition.
    lc_transition::wait_for_status(
        &jtag,
        Duration::from_secs(3),
        LcCtrlStatus::TRANSITION_SUCCESSFUL,
    )
    .context("failed to wait for LC to report TRANSITION_SUCCESSFUL status")?;

    // Lifecycle controller should now be in the POST_TRANSITION state.
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::PostTransition.redundant_encoding()
    );

    log::info!("Lifecycle transition complete");

    // No longer need the JTAG interface, shut down gracefully.
    jtag.disconnect()
        .context("failed to disconnect from JTAG")?;

    // Remove the RMA strapping so that future resets bring up normally.
    rma_bootstrap_strapping
        .remove()
        .context("failed to remove strapping RMA_BOOTSTRAP")?;

    // Remove the strapping in case this state survives to another test.
    tap_strapping
        .remove()
        .context("failed to remove strapping PINMUX_TAP_LC")?;

    // Reset again and check the lifecycle state is now `RMA` by reading for
    // "LCV:" on the UART.

    let uart = transport.uart("console").context("failed to get console")?;

    transport
        .reset_target(opts.init.bootstrap.options.reset_delay, true)
        .context("failed to reset target")?;

    let rma_state = DifLcCtrlState::Rma.redundant_encoding();
    let exit_success =
        Regex::new(format!("LCV:{rma_state:x}\r\n").as_str()).context("failed to build regex")?;
    let exit_failure = Regex::new("LCV:[0-9a-f]+\r\n").context("failed to build regex")?;

    let mut console = UartConsole {
        timeout: Some(CONSOLE_TIMEOUT),
        exit_success: Some(exit_success),
        exit_failure: Some(exit_failure),
        ..Default::default()
    };

    let mut stdout = io::stdout();
    let result = console
        .interact(&*uart, None, Some(&mut stdout))
        .context("failed to interact with console")?;

    match result {
        ExitStatus::ExitSuccess => Ok(()),
        result => bail!("FAIL: {result:?}"),
    }
}
