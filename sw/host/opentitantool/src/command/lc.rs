// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::rc::Rc;
use std::time::Duration;

use anyhow::{bail, Result};
use clap::{Args, Subcommand};
use hex::decode;
use humantime::parse_duration;
use serde_annotate::Annotate;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{Jtag, JtagParams, JtagTap};
use opentitanlib::test_utils::lc_transition::{trigger_lc_transition, trigger_volatile_raw_unlock};

#[derive(serde::Serialize)]
pub struct LcStateReadResult {
    pub lc_state: DifLcCtrlState,
}

/// Read, decode, and check the LC state is Raw.
fn check_lc_state_is_raw(jtag: Rc<dyn Jtag>) -> Result<()> {
    let lc_state = DifLcCtrlState(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?);
    if lc_state != DifLcCtrlState::Raw {
        bail!("Device must be in Raw LC state. It is in: {}", lc_state);
    }
    Ok(())
}

/// Parses an unlock token string.
fn parse_unlock_token_str(token: &str) -> Result<[u32; 4]> {
    let hex_str_no_sep = token.replace('_', "");
    let hex_str_prefix = "0x";
    let sanitized_hex_str = if token.starts_with(hex_str_prefix) {
        hex_str_no_sep.strip_prefix(hex_str_prefix).unwrap()
    } else {
        hex_str_no_sep.as_str()
    };
    let token_bytes_vec = decode(sanitized_hex_str)?;
    if token_bytes_vec.len() != 16 {
        bail!(
            "Expected a token of length 16-bytes but it was {}-bytes.",
            token_bytes_vec.len()
        );
    }
    let token_word_vec: Vec<u32> = token_bytes_vec
        .chunks_exact(std::mem::size_of::<u32>())
        .map(|chunk| u32::from_be_bytes(chunk.try_into().unwrap()))
        .rev()
        .collect();
    Ok(token_word_vec.try_into().unwrap())
}

#[derive(Debug, Args)]
/// Reads the device life cycle state over JTAG.
pub struct LcStateRead {
    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

impl CommandDispatch for LcStateRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let jtag = self.jtag_params.create(transport)?;
        jtag.connect(JtagTap::LcTap)?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Args)]
/// Initiates a device transition from Raw to TestUnlocked0.
pub struct RawUnlock {
    /// The raw unlock token hexstring.
    #[arg(long)]
    pub token: String,

    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

impl CommandDispatch for RawUnlock {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let jtag = self.jtag_params.create(transport)?;
        jtag.connect(JtagTap::LcTap)?;

        check_lc_state_is_raw(jtag.clone())?;
        let token_words = parse_unlock_token_str(self.token.as_str())?;

        // ROM execution is not enabled in the OTP so we can safely reconnect to
        // the LC TAP after the transition without risking the chip resetting.
        trigger_lc_transition(
            transport,
            jtag.clone(),
            DifLcCtrlState::TestUnlocked0,
            Some(token_words),
            /*use_external_clk=*/ true,
            self.reset_delay,
            /*reconnect_jtag_tap=*/ Some(JtagTap::LcTap),
        )?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Args)]
/// Reads the LC transition count register of the LC controller.
pub struct TransitionCount {
    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

#[derive(serde::Serialize)]
pub struct LcTransitionCountResult {
    pub transition_count: u32,
}

impl CommandDispatch for TransitionCount {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process, connect to the LC JTAG TAP, read register, and shutdown OpenOCD.
        let jtag = self.jtag_params.create(transport)?;
        jtag.connect(JtagTap::LcTap)?;
        let transition_count = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcTransitionCnt)?;
        jtag.disconnect()?;

        Ok(Some(Box::new(LcTransitionCountResult { transition_count })))
    }
}

#[derive(Debug, Args)]
/// Initiates a (volatile) device transition from Raw to TestUnlocked0.
pub struct VolatileRawUnlock {
    /// The raw unlock token hexstring.
    #[arg(long)]
    pub token: String,

    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

impl CommandDispatch for VolatileRawUnlock {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let jtag = self.jtag_params.create(transport)?;
        jtag.connect(JtagTap::LcTap)?;

        check_lc_state_is_raw(jtag.clone())?;
        let token_words = parse_unlock_token_str(self.token.as_str())?;

        // ROM execution is not enabled in the OTP so we can safely reconnect to
        // the LC TAP after the transition without risking the chip resetting.
        trigger_volatile_raw_unlock(
            transport,
            jtag.clone(),
            DifLcCtrlState::TestUnlocked0,
            Some(token_words),
            /*use_external_clk=*/ true,
            /*post_transition_tap=*/ JtagTap::LcTap,
        )?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// Commands for performing various device life cycle operations.
pub enum LcCommand {
    Read(LcStateRead),
    RawUnlock(RawUnlock),
    TransitionCount(TransitionCount),
    VolatileRawUnlock(VolatileRawUnlock),
}
