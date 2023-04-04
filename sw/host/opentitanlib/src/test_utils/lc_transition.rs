// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;
use std::thread;
use std::time::Duration;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::app::TransportWrapper;
use crate::chip::boolean::MultiBitBool8;
use crate::dif::lc_ctrl::{
    DifLcCtrlState, LcCtrlReg, LcCtrlStatus, LcCtrlTransitionCmd, LcCtrlTransitionCtrl,
};
use crate::impl_serializable_error;
use crate::io::jtag::{Jtag, JtagTap};

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

pub fn trigger_lc_transition(
    transport: &TransportWrapper,
    jtag: Rc<dyn Jtag>,
    target_lc_state: DifLcCtrlState,
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

    // Program the target LC state, i.e., Scrap.
    jtag.write_lc_ctrl_reg(
        &LcCtrlReg::TransitionTarget,
        target_lc_state.redundant_encoding(),
    )?;

    // Check correct target LC state was programmed.
    let target_lc_state_programmed = jtag.read_lc_ctrl_reg(&LcCtrlReg::TransitionTarget)?;
    if target_lc_state_programmed != target_lc_state.redundant_encoding() {
        return Err(LcTransitionError::TargetProgrammingFailed(target_lc_state_programmed).into());
    }

    // TODO: program the transition token for conditional transitions.

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
    let one_millis = Duration::from_millis(1);
    loop {
        let status = jtag.read_lc_ctrl_reg(&LcCtrlReg::Status)?;
        let status =
            LcCtrlStatus::from_bits(status).ok_or(LcTransitionError::InvalidState(status))?;

        if status.contains(LcCtrlStatus::TRANSITION_SUCCESSFUL) {
            break;
        }

        let expected_status =
            LcCtrlStatus::INITIALIZED | LcCtrlStatus::READY | LcCtrlStatus::TRANSITION_SUCCESSFUL;
        if status != expected_status {
            return Err(LcTransitionError::TransitionFailed(status).into());
        }
        thread::sleep(one_millis);
    }

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
