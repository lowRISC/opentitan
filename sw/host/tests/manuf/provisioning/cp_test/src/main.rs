// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use rand::RngCore;

use cp_lib::{
    hex_string_to_u32_arrayvec, reset_and_lock, run_sram_cp_provision, unlock_raw,
    ManufCpProvisioningData, Opts,
};
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::lc_transition;

fn cp_provision(
    opts: &Opts,
    transport: &TransportWrapper,
    provisioning_data: &ManufCpProvisioningData,
) -> Result<()> {
    unlock_raw(opts, transport)?;
    run_sram_cp_provision(opts, transport, provisioning_data)?;
    reset_and_lock(opts, transport)?;
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
    let jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_LOCKED0`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestLocked0.redundant_encoding());

    // ROM execution is not yet enabled in the OTP so we can safely reconnect to the LC TAP after
    // the transition without risking the chip resetting.
    lc_transition::trigger_lc_transition(
        transport,
        jtag.clone(),
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
        /*reconnect_jtag_tap=*/ Some(JtagTap::LcTap),
    )?;

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
    // Set the TAP straps for the CPU and reset.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Connect to the RISCV TAP via JTAG.
    let jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::RiscvTap)?;

    // TODO: Read and check device_id field from flash info page 0.
    // TODO: Read and check manuf_state field from flash info page 0.
    // TODO: Read and check wafer_auth_secret field from flash info page 3.
    // TODO: Read and check test exit token field from OTP secret0 partition.
    // TODO: Read and check test unlock token field from OTP secret0 partition.

    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    // Generate random provisioning values for testing.
    let mut device_id = ArrayVec::<u32, 8>::new();
    let mut manuf_state = ArrayVec::<u32, 8>::new();
    let mut wafer_auth_secret = ArrayVec::<u32, 8>::new();
    let mut test_exit_token = ArrayVec::<u32, 4>::new();
    let mut test_unlock_token = ArrayVec::<u32, 4>::new();
    for i in 0..8 {
        if i < 4 {
            test_exit_token.push(rand::thread_rng().next_u32());
            test_unlock_token.push(rand::thread_rng().next_u32());
        }
        device_id.push(rand::thread_rng().next_u32());
        manuf_state.push(rand::thread_rng().next_u32());
        wafer_auth_secret.push(rand::thread_rng().next_u32());
    }
    println!("{:?}", device_id);

    // Provision values into the chip.
    let provisioning_data = ManufCpProvisioningData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
        manuf_state: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.manuf_state.as_str())?,
        wafer_auth_secret: wafer_auth_secret,
        test_unlock_token: test_unlock_token,
        test_exit_token: test_exit_token,
    };
    cp_provision(&opts, &transport, &provisioning_data)?;

    // Transition to TEST_UNLOCKED1 and check provisioning operations over JTAG.
    test_unlock(&opts, &transport, &provisioning_data)?;
    check_cp_provisioning(&opts, &transport, &provisioning_data)?;

    Ok(())
}
