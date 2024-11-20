// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Context, Result};
use clap::{Args, Parser};
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::SecretKey;
use p256::NistP256;

use cert_lib::{CaConfig, CaKey, CaKeyType};
use ft_lib::{
    check_rom_ext_boot_up, run_ft_personalize, run_sram_ft_individualize, test_exit, test_unlock,
};
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

    /// TestUnlock token; a 128-bit hex string.
    #[arg(long)]
    pub test_unlock_token: String,

    /// TestExit token; a 128-bit hex string.
    #[arg(long)]
    pub test_exit_token: String,

    /// RMA unlock token; a 128-bit hex string.
    #[arg(long)]
    pub rma_unlock_token: String,

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
}

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[command(flatten)]
    sram_program: SramProgramParams,

    #[command(flatten)]
    provisioning_data: ManufFtProvisioningDataInput,

    /// CA HJSON configuration file.
    #[arg(long)]
    ca_config: PathBuf,

    /// Second image (perso FW + ROM_EXT/Owner FW bundle) to bootstrap.
    #[arg(long)]
    second_bootstrap: PathBuf,

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

    // Parse and format LC tokens.
    let _test_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_unlock_token.as_str())?;
    let _test_exit_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_exit_token.as_str())?;
    let rma_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.rma_unlock_token.as_str())?;

    // Parse and prepare individualization ujson data payload.
    let _ft_individualize_data_in = ManufFtIndividualizeData {
        device_id: hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.device_id.as_str())?,
    };

    // Parse and prepare CA key.
    let mut ca_cfgs: HashMap<String, CaConfig> = serde_annotate::from_str(
        &std::fs::read_to_string(opts.ca_config)
            .with_context(|| "Failed to open CA config JSON.")?,
    )?;
    let mut ca_keys = HashMap::<String, CaKey>::new();
    for (ca, cfg) in &mut ca_cfgs {
        ca_keys.insert(
            ca.to_string(),
            match cfg.key_type {
                CaKeyType::Raw => {
                    log::info!("Using raw key for cert endorsement.");
                    CaKey::RawKey(SecretKey::<NistP256>::read_pkcs8_der_file(
                        cfg.key.as_str(),
                    )?)
                }
                CaKeyType::Token => {
                    log::info!("Using PKCS#11 token key for cert endorsement.");
                    CaKey::TokenKey(cfg.key.clone())
                }
            },
        );
    }

    // Parse and prepare personalization ujson data payload.
    let rom_ext_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.rom_ext_measurement.as_str())?;
    let rom_ext_security_version = opts.provisioning_data.rom_ext_security_version;
    let owner_manifest_measurement = hex_string_to_u32_arrayvec::<8>(
        opts.provisioning_data.owner_manifest_measurement.as_str(),
    )?;
    let owner_measurement =
        hex_string_to_u32_arrayvec::<8>(opts.provisioning_data.owner_measurement.as_str())?;
    let owner_security_version = opts.provisioning_data.owner_security_version;
    let dice_ca_key_id = hex_string_to_u8_arrayvec::<20>(ca_cfgs["dice"].key_id.as_str())?;
    let ext_ca_key_id = hex_string_to_u8_arrayvec::<20>(ca_cfgs["ext"].key_id.as_str())?;
    let _perso_certgen_inputs = ManufCertgenInputs {
        rom_ext_measurement: rom_ext_measurement.clone(),
        rom_ext_security_version,
        owner_manifest_measurement: owner_manifest_measurement.clone(),
        owner_measurement: owner_measurement.clone(),
        owner_security_version,
        dice_auth_key_key_id: dice_ca_key_id.clone(),
        ext_auth_key_key_id: ext_ca_key_id.clone(),
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

    run_ft_personalize(
        &transport,
        &opts.init,
        &rma_unlock_token,
        ca_cfgs,
        ca_keys,
        &_perso_certgen_inputs,
        opts.second_bootstrap,
        &spi_console_device,
        opts.timeout,
    )?;

    check_rom_ext_boot_up(&transport, &opts.init, opts.timeout)?;
    log::info!("Provisioning Done");

    Ok(())
}
