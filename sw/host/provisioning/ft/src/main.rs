// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Result};
use clap::{Args, Parser};

use ft_lib::{run_ft_personalize, run_sram_ft_individualize, test_exit, test_unlock, KeyWrapper};
use opentitanlib::backend;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::dif::lc_ctrl::DifLcCtrlState;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc::read_lc_state;
use opentitanlib::test_utils::load_sram_program::SramProgramParams;
use ujson_lib::provisioning_data::{ManufCertgenInputs, ManufFtIndividualizeData};
use util_lib::{hex_string_to_u32_arrayvec, hex_string_to_u8_arrayvec};

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

    /// Measurement of the ROM_EXT image to be loaded onto the device.
    #[arg(long)]
    pub rom_ext_measurement: String,

    /// Security version the ROM_EXT image to be loaded onto the device.
    #[arg(long, default_value = "0")]
    pub rom_ext_security_version: u32,

    /// Measurement of the Ownership Manifest to be loaded onto the device.
    #[arg(long)]
    pub owner_manifest_measurement: String,

    /// Measurement of the Owner image to be loaded onto the device.
    #[arg(long)]
    pub owner_measurement: String,

    /// Security version the Owner image to be loaded onto the device.
    #[arg(long, default_value = "0")]
    pub owner_security_version: u32,

    /// CA (ECC P256) endorsement key as a DER file path.
    #[arg(long, default_value = None,  required = true, conflicts_with = "ca_key_ckms_id")]
    ca_key_der_file: Option<PathBuf>,

    /// CA endorsement key as a Google Cloud KMS key ID string.
    #[arg(long, default_value = None, required = true, conflicts_with = "ca_key_der_file")]
    pub ca_key_ckms_id: Option<String>,

    /// CA key ID hexstring.
    #[arg(long)]
    pub ca_key_id: String,

    /// CA certificate to be used for verifying a cert chain.
    #[arg(long)]
    pub ca_certificate: PathBuf,

    /// RMA unlock token hash to pass to the device, a string of 16 hex digits.
    #[arg(long)]
    pub rma_unlock_token_hash: String,
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufFtProvisioningDataInput,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    // We call the below functions, instead of calling `opts.init.init_target()` since we do not
    // want to perform bootstrap yet.
    let transport = backend::create(&opts.init.backend_opts)?;
    transport.apply_default_configuration(None)?;
    let spi = transport.spi(&opts.console_spi)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi)?;
    InitializeTest::print_result("load_bitstream", opts.init.load_bitstream.init(&transport))?;

    // Format test tokens.
    let _test_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_unlock_token.as_str())?;
    let _test_exit_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_exit_token.as_str())?;
    let rma_unlock_token_hash =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.rma_unlock_token_hash.as_str())?;
    // Format ujson data payload(s).
    // Individualization ujson payload.
    let _ft_individualize_data_in = ManufFtIndividualizeData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
    };
    // Personalization ujson payload.
    let rom_ext_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.rom_ext_measurement.as_str())?;
    let rom_ext_security_version = opts.provisioning_data.rom_ext_security_version;
    let owner_manifest_measurement = hex_string_to_u32_arrayvec::<8>(
        opts.provisioning_data.owner_manifest_measurement.as_str(),
    )?;
    let owner_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.owner_measurement.as_str())?;
    let owner_security_version = opts.provisioning_data.owner_security_version;
    let ca_key_id = hex_string_to_u8_arrayvec::<20>(opts.provisioning_data.ca_key_id.as_str())?;
    let _perso_certgen_inputs = ManufCertgenInputs {
        rom_ext_measurement: rom_ext_measurement.clone(),
        rom_ext_security_version,
        owner_manifest_measurement: owner_manifest_measurement.clone(),
        owner_measurement: owner_measurement.clone(),
        owner_security_version,
        auth_key_key_id: ca_key_id.clone(),
    };

    // Only run test unlock operation if we are in a locked LC state.
    match read_lc_state(
        &transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )? {
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
    match read_lc_state(
        &transport,
        &opts.init.jtag_params,
        opts.init.bootstrap.options.reset_delay,
    )? {
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
                &spi_console_device,
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

    // Once we are in a mission mode, we no longer need to provide a DFT strapping sequence on
    // every reset, as DFT is no longer enabled in mission modes.
    transport.ignore_dft_straps_on_reset()?;

    let cert_endorsement_key_wrapper = match (
        opts.provisioning_data.ca_key_ckms_id,
        opts.provisioning_data.ca_key_der_file,
    ) {
        (Some(ckms), None) => KeyWrapper::CkmsKey(ckms),
        (None, Some(local)) => KeyWrapper::LocalKey(local),
        (_, _) => {
            log::error!("One and only one endorsement key parameter must be included");
            bail!("Incorrect command line endorsement key settings");
        }
    };
    run_ft_personalize(
        &transport,
        &opts.init,
        cert_endorsement_key_wrapper,
        &_perso_certgen_inputs,
        opts.timeout,
        opts.provisioning_data.ca_certificate,
        &rma_unlock_token_hash,
        &spi_console_device,
    )?;

    log::info!("Provisioning Done");

    Ok(())
}
