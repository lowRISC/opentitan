// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Result};
use clap::{Args, Parser};

use ft_lib::{run_ft_personalize, run_sram_ft_individualize, test_exit, test_unlock};
use opentitanlib::backend;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::load_sram_program::SramProgramParams;
use ujson_lib::provisioning_data::{ManufCertPersoDataIn, ManufFtIndividualizeData};
use util_lib::hex_string_to_u32_arrayvec;

/// Provisioning data command-line parameters.
#[derive(Debug, Args, Clone)]
pub struct ManufFtProvisioningDataInput {
    /// Device ID to provision.
    ///
    /// Must match the device ID provisioned in to flash during CP, if one was provisioned then.
    #[arg(long)]
    pub device_id: String,

    /// TestUnlock token.
    #[arg(long)]
    pub test_unlock_token: String,

    /// TestExit token.
    #[arg(long)]
    pub test_exit_token: String,

    /// LC state to transition to from TEST_UNLOCKED*.
    #[arg(long, value_parser = DifLcCtrlState::parse_lc_state_str)]
    target_mission_mode_lc_state: DifLcCtrlState,

    /// Host (HSM) generated ECC (P256) private key DER file.
    #[arg(long)]
    host_ecc_sk: PathBuf,

    /// Measurement of the ROM_EXT image to be loaded onto the device.
    #[arg(long)]
    pub rom_ext_measurement: String,

    /// Measurement of the Ownership Manifest to be loaded onto the device.
    #[arg(long)]
    pub owner_manifest_measurement: String,

    /// Measurement of the Owner image to be loaded onto the device.
    #[arg(long)]
    pub owner_measurement: String,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufFtProvisioningDataInput,

    /// Second personalization binary to bootstrap.
    #[arg(long)]
    second_bootstrap: PathBuf,

    /// Third personalization binary to bootstrap.
    #[arg(long)]
    third_bootstrap: PathBuf,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    // We call the below functions, instead of calling `opts.init.init_target()` since we do not
    // want to perform bootstrap yet.
    let transport = backend::create(&opts.init.backend_opts)?;
    transport.apply_default_configuration(None)?;
    InitializeTest::print_result("load_bitstream", opts.init.load_bitstream.init(&transport))?;

    // Format test tokens.
    let _test_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_unlock_token.as_str())?;
    let _test_exit_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_exit_token.as_str())?;

    // Format ujson data payload(s).
    let _ft_individualize_data_in = ManufFtIndividualizeData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
    };
    let rom_ext_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.rom_ext_measurement.as_str())?;
    let owner_manifest_measurement = hex_string_to_u32_arrayvec::<8>(
        opts.provisioning_data.owner_manifest_measurement.as_str(),
    )?;
    let owner_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.owner_measurement.as_str())?;
    let _attestation_tcb_measurements = ManufCertPersoDataIn {
        rom_ext_measurement: rom_ext_measurement.clone(),
        owner_manifest_measurement: owner_manifest_measurement.clone(),
        owner_measurement: owner_measurement.clone(),
    };

    // Read the LC state.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    let mut jtag = opts
        .init
        .jtag_params
        .create(&transport)?
        .connect(JtagTap::LcTap)?;
    let lc_state =
        DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;
    jtag.disconnect()?;

    // Only run test unlock operation if we are in a locked LC state.
    match lc_state {
        DifLcCtrlState::TestLocked0
        | DifLcCtrlState::TestLocked1
        | DifLcCtrlState::TestLocked2
        | DifLcCtrlState::TestLocked3
        | DifLcCtrlState::TestLocked4
        | DifLcCtrlState::TestLocked5
        | DifLcCtrlState::TestLocked6 => {
            test_unlock(
                &transport,
                &opts.init.jtag_params,
                opts.init.bootstrap.options.reset_delay,
                &_test_unlock_token,
            )?;
        }
        _ => {
            log::info!("Skipping test unlock operation. Device is already unlocked.");
        }
    };

    // Only run the SRAM individualize program in a test unlocked state. If we have transitioned to
    // a mission state already, then we can skip this step.
    match lc_state {
        DifLcCtrlState::TestUnlocked0 => {
            bail!("FT stage cannot be run from test unlocked 0. Run CP stage first.");
        }
        DifLcCtrlState::TestUnlocked1
        | DifLcCtrlState::TestUnlocked2
        | DifLcCtrlState::TestUnlocked3
        | DifLcCtrlState::TestUnlocked4
        | DifLcCtrlState::TestUnlocked5
        | DifLcCtrlState::TestUnlocked6
        | DifLcCtrlState::TestUnlocked7 => {
            run_sram_ft_individualize(
                &transport,
                &opts.init.jtag_params,
                opts.init.bootstrap.options.reset_delay,
                &opts.sram_program,
                &_ft_individualize_data_in,
                opts.timeout,
            )?;
            test_exit(
                &transport,
                &opts.init.jtag_params,
                opts.init.bootstrap.options.reset_delay,
                &_test_exit_token,
                opts.provisioning_data.target_mission_mode_lc_state,
            )?;
        }
        _ => {
            log::info!("Skipping individualize operation. Device is already in a mission mode.");
        }
    };

    run_ft_personalize(
        &transport,
        &opts.init,
        opts.second_bootstrap,
        opts.third_bootstrap,
        opts.provisioning_data.host_ecc_sk,
        &_attestation_tcb_measurements,
        opts.timeout,
    )?;

    log::info!("Provisioning Done");

    Ok(())
}
