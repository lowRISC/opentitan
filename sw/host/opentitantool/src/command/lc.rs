// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use clap::{Args, Subcommand};
use hex::decode;
use humantime::parse_duration;
use serde_annotate::Annotate;
use std::any::Any;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::lc_transition;

#[derive(serde::Serialize)]
pub struct LcStateReadResult {
    pub lc_state: DifLcCtrlState,
}

#[derive(Debug, Args)]
/// Reads the device life cycle state over JTAG.
pub struct LcStateRead {
    /// Whether or not to use the externally provided clock.
    #[arg(long)]
    pub use_ext_clk: bool,

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
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Args)]
/// Initiates a device transition from Raw to TestUnlocked0.
pub struct RawUnlock {
    /// The raw unlock token hexstring.
    #[arg(long, default_value = "0x00000000_00000000_00000000_00000000")]
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

        // Read, decode, and check the LC state is Raw.
        let lc_state = DifLcCtrlState(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?);
        if lc_state != DifLcCtrlState::Raw {
            return Err(anyhow!(
                "Device must be in Raw LC state. It is in: {}",
                lc_state
            ));
        }

        // Parse unlock token.
        let hex_str_no_sep = self.token.replace('_', "");
        let hex_str_prefix = "0x";
        let sanitized_hex_str = if self.token.starts_with(hex_str_prefix) {
            hex_str_no_sep.strip_prefix(hex_str_prefix).unwrap()
        } else {
            hex_str_no_sep.as_str()
        };
        let token_bytes_vec = decode(sanitized_hex_str)?;
        let token_word_vec: Vec<u32> = token_bytes_vec
            .chunks_exact(std::mem::size_of::<u32>())
            .map(|chunk| u32::from_be_bytes(chunk.try_into().unwrap()))
            .rev()
            .collect();
        if token_word_vec.len() < 4 {
            return Err(anyhow!(
                "Expected a token of length 16-bytes but it was {}-bytes.",
                token_word_vec.len() * std::mem::size_of::<u32>()
            ));
        }
        let token_words: [u32; 4] = token_word_vec.try_into().unwrap();

        // ROM execution is not enabled in the OTP so we can safely reconnect to
        // the LC TAP after the transition without risking the chip resetting.
        lc_transition::trigger_lc_transition(
            transport,
            jtag.clone(),
            DifLcCtrlState::TestUnlocked0,
            Some(token_words),
            /*use_external_clk=*/ true,
            self.reset_delay,
            /*reconnect_jtag_tap=*/ Some(JtagTap::LcTap),
        )?;

        // Read and decode the LC state.
        let lc_state = DifLcCtrlState(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?);
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// Commands for performing various device life cycle operations.
pub enum LcCommand {
    Read(LcStateRead),
    RawUnlock(RawUnlock),
}
