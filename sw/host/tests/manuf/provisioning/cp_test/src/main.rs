// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use rand::RngCore;

use cp_lib::{reset_and_lock, run_sram_cp_provision, unlock_raw, ManufCpProvisioningDataInput};
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::UartSend;
use opentitanlib::uart::console::UartConsole;
use ujson_lib::provisioning_data::ManufCpProvisioningData;

#[derive(Debug, Parser)]
pub struct Opts {
    #[command(flatten)]
    pub init: InitializeTest,

    #[arg(long)]
    pub provisioning_sram_elf: Option<PathBuf>,

    #[arg(long)]
    pub test_sram_elf: Option<PathBuf>,

    #[command(flatten)]
    pub provisioning_data: ManufCpProvisioningDataInput,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    pub timeout: Duration,
}

fn cp_provision(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
) -> Result<()> {
    let provisioning_sram_program: SramProgramParams = SramProgramParams {
        elf: opts.provisioning_sram_elf.clone(),
        ..Default::default()
    };
    unlock_raw(
        transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )?;
    run_sram_cp_provision(
        transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
        &provisioning_sram_program,
        provisioning_data,
        opts.timeout,
    )?;
    reset_and_lock(
        transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )?;
    Ok(())
}

fn test_unlock(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
) -> Result<()> {
    // Connect to LC TAP.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_LOCKED0`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestLocked0.redundant_encoding());

    // ROM execution is not yet enabled in the OTP so we can safely reconnect to the LC TAP after
    // the transition without risking the chip resetting.
    lc_transition::trigger_lc_transition(
        transport,
        jtag,
        DifLcCtrlState::TestUnlocked1,
        Some(
            provisioning_data
                .test_unlock_token
                .clone()
                .into_inner()
                .unwrap(),
        ),
        /*use_external_clk=*/ true,
        opts.init.bootstrap.options.reset_delay,
        /*reset_tap_straps=*/ Some(JtagTap::LcTap),
    )?;

    jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;

    // Check that LC state has transitioned to `TestUnlocked1`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked1.redundant_encoding());

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

fn check_cp_provisioning(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
) -> Result<()> {
    let test_sram_program: SramProgramParams = SramProgramParams {
        elf: opts.test_sram_elf.clone(),
        ..Default::default()
    };

    // Set the TAP straps for the CPU and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Connect to the RISCV TAP via JTAG.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = test_sram_program.load_and_execute(&mut *jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Get UART, set flow control, and wait for test to start running.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(
        &*uart,
        r"Waiting for expected CP provisioning data ...",
        opts.timeout,
    )?;

    // Inject ground truth provisioning data into the device.
    provisioning_data.send(&*uart)?;

    // Wait for test complete.
    let _ = UartConsole::wait_for(&*uart, r"Checks complete. Success.", opts.timeout)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Generate random provisioning values for testing.
    let mut device_id = ArrayVec::new();
    let mut manuf_state = ArrayVec::new();
    let mut wafer_auth_secret = ArrayVec::new();
    let mut test_exit_token = ArrayVec::new();
    let mut test_unlock_token = ArrayVec::new();
    for i in 0..8 {
        if i < 4 {
            test_exit_token.push(rand::thread_rng().next_u32());
            test_unlock_token.push(rand::thread_rng().next_u32());
        }
        device_id.push(rand::thread_rng().next_u32());
        manuf_state.push(rand::thread_rng().next_u32());
        wafer_auth_secret.push(rand::thread_rng().next_u32());
    }

    // Provision values into the chip.
    let provisioning_data = ManufCpProvisioningData {
        device_id,
        manuf_state,
        wafer_auth_secret,
        test_unlock_token,
        test_exit_token,
    };
    cp_provision(&opts, &transport, &provisioning_data)?;

    // Transition to TEST_UNLOCKED1 and check provisioning operations over JTAG.
    test_unlock(&opts, &transport, &provisioning_data)?;
    check_cp_provisioning(&opts, &transport, &provisioning_data)?;

    Ok(())
}
