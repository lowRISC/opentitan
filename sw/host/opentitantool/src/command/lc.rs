// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::time::Duration;

use anyhow::{ensure, Result};
use clap::{Args, Subcommand};
use hex::decode;
use humantime::parse_duration;
use serde_annotate::Annotate;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, DifLcCtrlToken, LcCtrlReg, LcCtrlStatus};
use opentitanlib::io::jtag::{Jtag, JtagParams, JtagTap};
use opentitanlib::test_utils::lc_transition::{trigger_lc_transition, trigger_volatile_raw_unlock};

#[derive(serde::Serialize)]
pub struct LcStateReadResult {
    pub lc_state: DifLcCtrlState,
}

/// Read and decode the current life cycle state, and check whether the requested transition is valid.
fn check_lc_transition(
    jtag: &mut dyn Jtag,
    target: DifLcCtrlState,
    token: DifLcCtrlToken,
) -> Result<()> {
    let lc_state =
        DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;
    let check = lc_state.check_transition(target);
    ensure!(
        check.valid,
        "Invalid transition from {lc_state} to {target}."
    );
    if check.token {
        ensure!(
            !token.is_zero(),
            "Transition from {lc_state} to {target} requires a non-zero token."
        );
    } else {
        ensure!(
            token.is_zero(),
            "Transition from {lc_state} to {target} requires the token to be all-zeroes."
        );
    }
    Ok(())
}

/// Parses an unlock token string.
fn parse_token_str(token: &str) -> Result<DifLcCtrlToken> {
    let hex_str_no_sep = token.replace('_', "");
    let hex_str_prefix = "0x";
    let sanitized_hex_str = if token.starts_with(hex_str_prefix) {
        hex_str_no_sep.strip_prefix(hex_str_prefix).unwrap()
    } else {
        hex_str_no_sep.as_str()
    };
    let token_bytes_vec = decode(sanitized_hex_str)?
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<Vec<u32>>();
    let length = token_bytes_vec.len();
    ensure!(
        length == 4,
        "Expected a token of length 16-bytes but it was {length}-bytes."
    );
    Ok(DifLcCtrlToken::from(token_bytes_vec))
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
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(serde::Serialize)]
pub struct LcRegReadResult {
    pub value: String,
}

#[derive(Debug, Args)]
/// Reads the device life cycle state over JTAG.
pub struct LcRegRead {
    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,

    #[arg(value_enum)]
    pub reg: LcCtrlReg,
}

impl CommandDispatch for LcRegRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // Read the CSR
        let value = jtag.read_lc_ctrl_reg(&self.reg)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcRegReadResult {
            value: format!("{:#x}", value),
        })))
    }
}

#[derive(Debug, Args)]
/// Reads the 256bit device ID over JTAG.
pub struct LcDeviceIdRead {
    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

impl CommandDispatch for LcDeviceIdRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // Read and concatenate device ID registers.
        let offsets = [
            LcCtrlReg::DeviceId7,
            LcCtrlReg::DeviceId6,
            LcCtrlReg::DeviceId5,
            LcCtrlReg::DeviceId4,
            LcCtrlReg::DeviceId3,
            LcCtrlReg::DeviceId2,
            LcCtrlReg::DeviceId1,
            LcCtrlReg::DeviceId0,
        ];

        let mut value = vec![String::from("0x")];
        for off in offsets {
            value.push(format!("{:08x}", jtag.read_lc_ctrl_reg(&off)?));
        }

        jtag.disconnect()?;
        Ok(Some(Box::new(LcRegReadResult {
            value: value.join(""),
        })))
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
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        let token = parse_token_str(self.token.as_str())?;
        check_lc_transition(&mut *jtag, DifLcCtrlState::TestUnlocked0, token)?;

        // ROM execution is not enabled in the OTP so we can safely reconnect to
        // the LC TAP after the transition without risking the chip resetting.
        trigger_lc_transition(
            transport,
            jtag,
            DifLcCtrlState::TestUnlocked0,
            Some(token.into_register_values()),
            /*use_external_clk=*/ true,
            self.reset_delay,
            /*reset_tap_straps=*/ Some(JtagTap::LcTap),
        )?;

        jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Args)]
/// Resets the chip and initiates a transition into the specified target state.
pub struct Transition {
    /// The target life cycle state
    #[arg(value_enum, value_parser = DifLcCtrlState::parse_lc_state_str, default_value = "test_unlocked0")]
    pub target_lc_state: DifLcCtrlState,

    /// The token needed for this transition as a hexstring.
    #[arg(long, default_value = "0x00000000000000000000000000000000")]
    pub token: String,

    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

impl CommandDispatch for Transition {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process and connect to the LC JTAG TAP.
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // In order to be on the safe side, we're asserting ROM bootstrap and
        // reset the chip to prevent ROM from going into a reset loop.
        let rom_bootstrap = transport.pin_strapping("ROM_BOOTSTRAP")?;
        rom_bootstrap.apply()?;

        // Reset the chip so that LC_CTRL is in a clean state.
        let _ = transport.reset_target(Duration::from_millis(50), false);
        std::thread::sleep(Duration::from_millis(50));

        // Check whether this is a valid transition.
        let token = parse_token_str(self.token.as_str())?;
        check_lc_transition(&mut *jtag, self.target_lc_state, token)?;

        trigger_lc_transition(
            transport,
            jtag,
            self.target_lc_state,
            Some(token.into_register_values()),
            /*use_external_clk=*/ true,
            self.reset_delay,
            /*reset_tap_straps=*/ Some(JtagTap::LcTap),
        )?;

        jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        // Read and decode the LC state.
        let lc_state =
            DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;

        jtag.disconnect()?;
        rom_bootstrap.remove()?;
        Ok(Some(Box::new(LcStateReadResult { lc_state })))
    }
}

#[derive(Debug, Args)]
/// Reads the LC controller's status register.
pub struct Status {
    /// Reset duration when switching the LC TAP straps.
    #[arg(long, value_parser = parse_duration, default_value = "100ms")]
    pub reset_delay: Duration,

    #[command(flatten)]
    pub jtag_params: JtagParams,
}

#[derive(serde::Serialize)]
pub struct LcStatusResult {
    pub initialized: bool,
    pub ready: bool,
    pub ext_clock_switched: bool,
    pub transition_successful: bool,
    pub transition_count_error: bool,
    pub transition_error: bool,
    pub token_error: bool,
    pub flash_rma_error: bool,
    pub otp_error: bool,
    pub state_error: bool,
    pub bus_integrity_error: bool,
    pub otp_partition_error: bool,
}

impl CommandDispatch for Status {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Set the TAP straps for the lifecycle controller and reset.
        transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
        transport.reset_target(self.reset_delay, true)?;

        // Spawn an OpenOCD process, connect to the LC JTAG TAP, read register, and shutdown OpenOCD.
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;
        let status = jtag.read_lc_ctrl_reg(&LcCtrlReg::Status)?;
        jtag.disconnect()?;

        Ok(Some(Box::new(LcStatusResult {
            initialized: (status & LcCtrlStatus::INITIALIZED.bits()) != 0,
            ready: (status & LcCtrlStatus::READY.bits()) != 0,
            ext_clock_switched: (status & LcCtrlStatus::EXT_CLOCK_SWITCHED.bits()) != 0,
            transition_successful: (status & LcCtrlStatus::TRANSITION_SUCCESSFUL.bits()) != 0,
            transition_count_error: (status & LcCtrlStatus::TRANSITION_COUNT_ERROR.bits()) != 0,
            transition_error: (status & LcCtrlStatus::TRANSITION_ERROR.bits()) != 0,
            token_error: (status & LcCtrlStatus::TOKEN_ERROR.bits()) != 0,
            flash_rma_error: (status & LcCtrlStatus::FLASH_RMA_ERROR.bits()) != 0,
            otp_error: (status & LcCtrlStatus::OTP_ERROR.bits()) != 0,
            state_error: (status & LcCtrlStatus::STATE_ERROR.bits()) != 0,
            bus_integrity_error: (status & LcCtrlStatus::BUS_INTEG_ERROR.bits()) != 0,
            otp_partition_error: (status & LcCtrlStatus::OTP_PARTITION_ERROR.bits()) != 0,
        })))
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
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;
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
        let mut jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

        let token = parse_token_str(self.token.as_str())?;
        check_lc_transition(&mut *jtag, DifLcCtrlState::TestUnlocked0, token)?;

        // ROM execution is not enabled in the OTP so we can safely reconnect to
        // the LC TAP after the transition without risking the chip resetting.
        trigger_volatile_raw_unlock(
            transport,
            jtag,
            DifLcCtrlState::TestUnlocked0,
            Some(token.into_register_values()),
            /*use_external_clk=*/ true,
            /*post_transition_tap=*/ JtagTap::LcTap,
            &self.jtag_params,
            // whether we expect the RAW unlock feature to be present or not.
            // on prod silicon this should be disabled.
            false,
        )?;

        jtag = self
            .jtag_params
            .create(transport)?
            .connect(JtagTap::LcTap)?;

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
    RegRead(LcRegRead),
    DeviceIdRead(LcDeviceIdRead),
    RawUnlock(RawUnlock),
    Transition(Transition),
    Status(Status),
    TransitionCount(TransitionCount),
    VolatileRawUnlock(VolatileRawUnlock),
}
