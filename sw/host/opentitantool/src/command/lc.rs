// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use humantime::parse_duration;
use serde_annotate::Annotate;
use std::any::Any;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};

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

#[derive(Debug, Subcommand, CommandDispatch)]
/// Commands for performing various device life cycle operations.
pub enum LcCommand {
    Read(LcStateRead),
}
