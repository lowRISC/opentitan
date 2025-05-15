// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use rand::RngCore;
use zerocopy::IntoBytes;

use cp_lib::{CpResponse, reset_and_lock, run_sram_cp_provision, unlock_raw};
use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::ConsoleSend;
use opentitanlib::uart::console::UartConsole;
use ot_hal::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use ujson_lib::provisioning_data::{ManufCpProvisioningData, ManufCpTestData};
use util_lib::hash_lc_token;

#[derive(Debug, Parser)]
pub struct Opts {
    #[command(flatten)]
    pub init: InitializeTest,

    #[arg(long)]
    pub provisioning_sram_elf: Option<PathBuf>,

    #[arg(long)]
    pub test_sram_elf: Option<PathBuf>,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "IOA5")]
    console_tx_indicator_pin: String,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    pub timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,
}

fn cp_provision(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
    response: &mut CpResponse,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    let provisioning_sram_program: SramProgramParams = SramProgramParams {
        elf: opts.provisioning_sram_elf.clone(),
        ..Default::default()
    };
    run_sram_cp_provision(
        transport,
        &opts.init.jtag_params,
        &provisioning_sram_program,
        provisioning_data,
        spi_console,
        response,
        opts.timeout,
    )?;
    reset_and_lock(transport, &opts.init.jtag_params)?;
    Ok(())
}

fn test_unlock(
    opts: &Opts,
    transport: &TransportWrapper,
    test_unlock_token: Option<[u32; 4]>,
) -> Result<()> {
    // Connect to LC TAP.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset(UartRx::Clear)?;
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
        test_unlock_token,
        /*use_external_clk=*/ true,
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

fn prep_flash_for_cp_init(
    opts: &Opts,
    transport: &TransportWrapper,
    test_data: &ManufCpTestData,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    let test_sram_program: SramProgramParams = SramProgramParams {
        elf: opts.test_sram_elf.clone(),
        ..Default::default()
    };
    // Reset the SPI console before loading the target firmware.
    spi_console.reset_frame_counter();

    // Set the TAP straps for the CPU and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset(UartRx::Clear)?;

    // Connect to the RISCV TAP via JTAG.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state.
    jtag.reset(/*run=*/ false)?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = test_sram_program.load_and_execute(&mut *jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Wait for test to start running.
    let _ = UartConsole::wait_for(spi_console, r"Waiting for CP test data ...", opts.timeout)?;

    // Inject ground truth provisioning data into the device.
    test_data.send(spi_console)?;

    // Wait for test complete.
    let _ = UartConsole::wait_for(spi_console, r"Flash info page 0 programmed.", opts.timeout)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    Ok(())
}

fn check_cp_provisioning(
    opts: &Opts,
    transport: &TransportWrapper,
    test_data: &ManufCpTestData,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    // Reset the SPI console before loading the target firmware.
    spi_console.reset_frame_counter();

    let test_sram_program: SramProgramParams = SramProgramParams {
        elf: opts.test_sram_elf.clone(),
        ..Default::default()
    };

    // Set the TAP straps for the CPU and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset(UartRx::Clear)?;

    // Connect to the RISCV TAP via JTAG.
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = test_sram_program.load_and_execute(&mut *jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Wait for test to start running.
    let _ = UartConsole::wait_for(spi_console, r"Waiting for CP test data ...", opts.timeout)?;

    // Inject ground truth provisioning data into the device.
    test_data.send(spi_console)?;

    // Wait for test complete.
    let _ = UartConsole::wait_for(spi_console, r"Checks complete. Success.", opts.timeout)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    let spi = transport.spi(&opts.console_spi)?;
    let device_console_tx_ready_pin = &transport.gpio_pin(&opts.console_tx_indicator_pin)?;
    device_console_tx_ready_pin.set_mode(PinMode::Input)?;
    device_console_tx_ready_pin.set_pull_mode(PullMode::None)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, Some(device_console_tx_ready_pin))?;

    // Transition from RAW to TEST_UNLOCKED0.
    unlock_raw(&transport, &opts.init.jtag_params)?;

    // Generate random test wafer data.
    let test_data = ManufCpTestData {
        lot_name: rand::thread_rng().next_u32(),
        wafer_number: rand::thread_rng().next_u32(),
        wafer_x_coord: rand::thread_rng().next_u32(),
        wafer_y_coord: rand::thread_rng().next_u32(),
    };

    // CP response to log to console in JSON format.
    let mut response = CpResponse::default();

    // Prep flash info page 0 with wafer data, CP device ID, and AST configs.
    prep_flash_for_cp_init(&opts, &transport, &test_data, &spi_console_device)?;

    // Generate random CP inputs for testing.
    let mut wafer_auth_secret = ArrayVec::new();
    let mut test_exit_token: ArrayVec<u32, 4> = ArrayVec::new();
    let mut test_unlock_token: ArrayVec<u32, 4> = ArrayVec::new();
    for i in 0..8 {
        if i < 4 {
            test_exit_token.push(rand::thread_rng().next_u32());
            test_unlock_token.push(rand::thread_rng().next_u32());
        }
        wafer_auth_secret.push(rand::thread_rng().next_u32());
    }

    // Provision test tokens, WAS, and extract CP device ID.
    let provisioning_data = ManufCpProvisioningData {
        wafer_auth_secret,
        test_unlock_token_hash: hash_lc_token(test_unlock_token.as_bytes())?,
        test_exit_token_hash: hash_lc_token(test_exit_token.as_bytes())?,
    };
    cp_provision(
        &opts,
        &transport,
        &provisioning_data,
        &mut response,
        &spi_console_device,
    )?;

    // Transition to TEST_UNLOCKED1 and check provisioning operations.
    test_unlock(
        &opts,
        &transport,
        Some(test_unlock_token.into_inner().unwrap()),
    )?;
    check_cp_provisioning(&opts, &transport, &test_data, &spi_console_device)?;

    let doc = serde_json::to_string(&response)?;
    println!("CHIP_PROBE_DATA: {doc}");

    Ok(())
}
