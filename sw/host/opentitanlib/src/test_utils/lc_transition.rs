// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::iter;
use std::rc::Rc;
use std::time::Duration;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::chip::boolean::MultiBitBool8;
use crate::dif::lc_ctrl::{
    DifLcCtrlState, LcCtrlReg, LcCtrlStatus, LcCtrlTransitionCmd, LcCtrlTransitionCtrl,
};
use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, JtagTap};
use crate::test_utils::poll;

use top_earlgrey::top_earlgrey_memory;

/// Errors related to performing an LcTransition.
#[derive(Error, Debug, Deserialize, Serialize)]
pub enum LcTransitionError {
    #[error("LC controller not ready to perform an LC transition (status: {0:x}).")]
    LcCtrlNotReady(LcCtrlStatus),
    #[error("LC transition mutex was already claimed.")]
    MutexAlreadyClaimed,
    #[error("Failed to claim LC transition mutex.")]
    FailedToClaimMutex,
    #[error("LC transition target programming failed (target state: {0:x}).")]
    TargetProgrammingFailed(u32),
    #[error("LC transition failed (status: {0:x}).")]
    TransitionFailed(LcCtrlStatus),
    #[error("Bad post transition LC state: {0:x}.")]
    BadPostTransitionState(u32),
    #[error("Invalid LC state: {0:x}")]
    InvalidState(u32),
    #[error("Generic error {0}")]
    Generic(String),
}
impl_serializable_error!(LcTransitionError);

/// Perform a lifecycle transition through the JTAG interface to the LC CTRL.
///
/// Requires the `jtag` to be already connected to the LC TAP.
/// The device will be reset into the new lifecycle state.
///
/// # Examples
///
/// ```rust
/// let init: InitializedTest;
/// let transport = init.init_target().unwrap();
///
/// // Set TAP strapping to the LC controller.
/// let tap_lc_strapping = transport.pin_strapping("PINMUX_TAP_LC").unwrap();
/// tap_lc_strapping.apply().expect("failed to apply strapping");
///
/// // Reset into the new strapping.
/// transport.reset_target(init.bootstrap.options.reset_delay, true).unwrap();
///
/// // Connect to the LC controller TAP.
/// let jtag = transport.jtag(jtag_opts).unwrap();
/// jtag.connect(JtagTap::LcTap).expect("failed to connect to LC TAP");
///
/// let test_exit_token = DifLcCtrlToken::from([0xff; 16]);
///
/// lc_transition::trigger_lc_transition(
///     &transport,
///     jtag.clone(),
///     DifLcCtrlState::Prod,
///     Some(test_exit_token.into_register_values()),
///     true,
///     init.bootstrap.options.reset_delay,
/// ).expect("failed to trigger transition to prod");
///
/// assert_eq!(
///     jtag.read_lc_ctrl_reg(&LcCtrlReg::LCState).unwrap(),
///     DifLcCtrlState::Prod.redundant_encoding(),
/// );
/// ```
pub fn trigger_lc_transition(
    transport: &TransportWrapper,
    jtag: Rc<dyn Jtag>,
    target_lc_state: DifLcCtrlState,
    token: Option<[u32; 4]>,
    use_external_clk: bool,
    reset_delay: Duration,
) -> Result<()> {
    // Check the lc_ctrl is initialized and ready to accept a transition request.
    let status = jtag.read_lc_ctrl_reg(&LcCtrlReg::Status)?;
    let status = LcCtrlStatus::from_bits(status).ok_or(LcTransitionError::InvalidState(status))?;
    if status != LcCtrlStatus::INITIALIZED | LcCtrlStatus::READY {
        return Err(LcTransitionError::LcCtrlNotReady(status).into());
    }

    // Check the LC transition mutex has not been claimed yet.
    if jtag.read_lc_ctrl_reg(&LcCtrlReg::ClaimTransitionIf)? == u8::from(MultiBitBool8::True) as u32
    {
        return Err(LcTransitionError::MutexAlreadyClaimed.into());
    }

    // Attempt to claim the LC transition mutex.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::ClaimTransitionIf,
        u8::from(MultiBitBool8::True) as u32,
    )?;

    // Check the LC transition mutex was claimed.
    if jtag.read_lc_ctrl_reg(&LcCtrlReg::ClaimTransitionIf)? != u8::from(MultiBitBool8::True) as u32
    {
        return Err(LcTransitionError::FailedToClaimMutex.into());
    }

    // Program the target LC state.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::TransitionTarget,
        target_lc_state.redundant_encoding(),
    )?;

    // Check correct target LC state was programmed.
    let target_lc_state_programmed = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionTarget)?;
    if target_lc_state_programmed != target_lc_state.redundant_encoding() {
        return Err(LcTransitionError::TargetProgrammingFailed(target_lc_state_programmed).into());
    }

    // If the transition requires a token, write it to the multi-register.
    if let Some(token_words) = token {
        let token_regs = [
            &LcCtrlReg::TransitionToken0,
            &LcCtrlReg::TransitionToken1,
            &LcCtrlReg::TransitionToken2,
            &LcCtrlReg::TransitionToken3,
        ];

        for (reg, value) in iter::zip(token_regs, token_words) {
            jtag.write_lc_ctrl_reg(reg, value)?;
        }
    }

    // Configure external clock.
    if use_external_clk {
        jtag.write_lc_ctrl_reg(
            &LcCtrlReg::TransitionCtrl,
            LcCtrlTransitionCtrl::EXT_CLOCK_EN.bits(),
        )?;
    } else {
        jtag.write_lc_ctrl_reg(&LcCtrlReg::TransitionCtrl, 0)?;
    }

    // Initiate LC transition and poll status register until transition is completed.
    jtag.write_lc_ctrl_reg(&LcCtrlReg::TransitionCmd, LcCtrlTransitionCmd::START.bits())?;

    wait_for_status(
        &jtag,
        Duration::from_secs(3),
        LcCtrlStatus::TRANSITION_SUCCESSFUL,
    )
    .context("failed waiting for TRANSITION_SUCCESSFUL status.")?;

    // Check we have entered the post transition state.
    let post_transition_lc_state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    if post_transition_lc_state != DifLcCtrlState::PostTransition.redundant_encoding() {
        return Err(LcTransitionError::BadPostTransitionState(post_transition_lc_state).into());
    }

    // Reset the chip, keeping LC TAP selected.
    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(reset_delay, true)?;
    jtag.connect(JtagTap::LcTap)?;

    Ok(())
}

pub fn wait_for_status(jtag: &Rc<dyn Jtag>, timeout: Duration, status: LcCtrlStatus) -> Result<()> {
    let jtag_tap = jtag.get_tap().unwrap();

    // Wait for LC controller to be ready.
    poll::poll_until(timeout, Duration::from_millis(50), || {
        let polled_status = match jtag_tap {
            JtagTap::LcTap => jtag.read_lc_ctrl_reg(&LcCtrlReg::Status).unwrap(),
            JtagTap::RiscvTap => {
                let mut status = [0u32];
                jtag.read_memory32(
                    top_earlgrey_memory::TOP_EARLGREY_LC_CTRL_BASE_ADDR as u32
                        + LcCtrlReg::Status as u32,
                    &mut status,
                )?;
                status[0]
            }
        };

        let polled_status =
            LcCtrlStatus::from_bits(polled_status).context("status has invalid bits set")?;

        // Check for any error bits set.
        if polled_status.intersects(LcCtrlStatus::ERRORS) {
            bail!("status {polled_status:#b} has error bits set");
        }

        Ok(polled_status.contains(status))
    })
}
