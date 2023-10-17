// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::{ArgAction, Args};

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::test_utils::status::Status;
use opentitanlib::uart::console::UartConsole;
use ujson_lib::provisioning_command::{FtIndividualizeCommand, FtPersonalizeCommand};

/// Provisioning action command-line parameters, namely, the provisioning commands to send.
#[derive(Debug, Args, Clone)]
pub struct ManufFtProvisioningActions {
    #[arg(
        long,
        action = ArgAction::SetTrue,
        help = "Whether to perform all FT provisioning steps."
    )]
    pub all_steps: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether to transition from TEST_LOCKED0 to TEST_UNLOCKED1 LC state."
    )]
    pub test_unlock: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether to write the OTP CREATOR_SW_CFG partition."
    )]
    pub otp_creator_sw_cfg: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether the OTP OWNER_SW_CFG partition."
    )]
    pub otp_owner_sw_cfg: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether to write the OTP HW_CFG partition."
    )]
    pub otp_hw_cfg: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether to transition to a mission mode state (specified by another arg) after provisioning is complete."
    )]
    pub test_exit: bool,

    #[arg(
        long,
        action = ArgAction::SetTrue,
        conflicts_with = "all_steps",
        help = "Whether to personalize the device with secrets.",
    )]
    pub personalize: bool,
}

pub fn test_unlock(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
    test_unlock_token: &ArrayVec<u32, 4>,
) -> Result<()> {
    // Connect to LC TAP.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(reset_delay, true)?;
    let jtag = jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_LOCKED0`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestLocked0.redundant_encoding());

    // ROM execution is not yet enabled in OTP so we can safely reconnect to the LC TAP after
    // the transition without risking the chip resetting.
    trigger_lc_transition(
        transport,
        jtag.clone(),
        DifLcCtrlState::TestUnlocked1,
        Some(test_unlock_token.clone().into_inner().unwrap()),
        /*use_external_clk=*/
        false, // AST will be calibrated by now, so no need for ext_clk.
        reset_delay,
        /*reconnect_jtag_tap=*/ Some(JtagTap::LcTap),
    )?;

    // Check that LC state has transitioned to `TestUnlocked1`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked1.redundant_encoding());

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

pub fn run_sram_ft_individualize(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
    sram_program: &SramProgramParams,
    provisioning_actions: &ManufFtProvisioningActions,
    timeout: Duration,
) -> Result<()> {
    // Set CPU TAP straps, reset, and connect to the JTAG interface.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(reset_delay, true)?;
    let jtag = jtag_params.create(transport)?;
    jtag.connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = sram_program.load_and_execute(&jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Get UART, set flow control, and wait for test to start running.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(
        &*uart,
        r"FT SRAM provisioning start. Waiting for command ...",
        timeout,
    )?;

    // Inject provisioning commands.
    if provisioning_actions.all_steps {
        FtIndividualizeCommand::WriteAll.send(&*uart)?;
        Status::recv(&*uart, timeout, false)?;
    }
    if provisioning_actions.otp_creator_sw_cfg {
        FtIndividualizeCommand::OtpCreatorSwCfgWrite.send(&*uart)?;
        Status::recv(&*uart, timeout, false)?;
    }
    if provisioning_actions.otp_owner_sw_cfg {
        FtIndividualizeCommand::OtpOwnerSwCfgWrite.send(&*uart)?;
        Status::recv(&*uart, timeout, false)?;
    }
    if provisioning_actions.otp_hw_cfg {
        FtIndividualizeCommand::OtpHwCfgWrite.send(&*uart)?;
        Status::recv(&*uart, timeout, false)?;
    }
    FtIndividualizeCommand::Done.send(&*uart)?;
    Status::recv(&*uart, timeout, false)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    Ok(())
}

pub fn test_exit(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
    test_exit_token: &ArrayVec<u32, 4>,
    target_mission_mode_lc_state: DifLcCtrlState,
) -> Result<()> {
    // Connect to LC TAP.
    //
    // We purposely DO NOT reset the chip here, as the FT provisioning SRAM progam that was just
    // executed should have unlocked ROM execution and halted the CPU already. If we reset the
    // chip, the ROM will attempt to boot the flash image, which we do not want to do until we
    // transition to a mission mode state. We do not need to reset the chip to switch TAPs because
    // TAP straps are continuously sampled in TEST_UNLOCKED* LC state.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    let jtag = jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_UNLOCKED1`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked1.redundant_encoding());

    // ROM execution should now be enabled in OTP so we cannot safely reconnect to the LC TAP after
    // the transition without risking the chip resetting. Therefore, it is the responsibility of the
    // flash program that is subsequently bootstrapped / run to check the LC state is as expected.
    trigger_lc_transition(
        transport,
        jtag.clone(),
        target_mission_mode_lc_state,
        Some(test_exit_token.clone().into_inner().unwrap()),
        /*use_external_clk=*/
        false, // AST will be calibrated by now, so no need for ext_clk.
        reset_delay,
        /*reconnect_jtag_tap=*/ None,
    )?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    timeout: Duration,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Bootstrap test program into flash and wait for test status pass over the UART.
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    // Get UART, set flow control, and wait for test to start running.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(
        &*uart,
        r"FT personalization start. Waiting for command ...",
        timeout,
    )?;

    // Inject provisioning commands.
    FtPersonalizeCommand::Done.send(&*uart)?;
    Status::recv(&*uart, timeout, false)?;

    Ok(())
}
