// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use arrayvec::ArrayVec;
use base64ct::{Base64, Encoding};
use clap::{Args, Parser};
use elliptic_curve::SecretKey;
use elliptic_curve::pkcs8::DecodePrivateKey;
use indexmap::IndexMap;
use p256::NistP256;

use cert_lib::{CaConfig, CaKey, CaKeyType};
use ft_lib::response::PersonalizeResponse;
use ft_lib::{
    check_slot_b_boot_up, run_ft_personalize, run_sram_ft_individualize, test_exit, test_unlock,
};
use opentitanlib::backend;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc::{read_device_id, read_lc_state};
use opentitanlib::test_utils::load_sram_program::SramProgramParams;
use ot_hal::dif::lc_ctrl::DifLcCtrlState;
use ujson_lib::UjsonPayloads;
use ujson_lib::provisioning_data::ManufCertgenInputs;
use util_lib::{
    encrypt_token, hex_string_to_u8_arrayvec, hex_string_to_u32_arrayvec, load_rsa_public_key,
    random_token,
};

/// Provisioning data command-line parameters.
#[derive(Debug, Args, Clone)]
pub struct ManufFtProvisioningDataInput {
    /// Wafer Authentication Secret to verify from device.
    #[arg(long)]
    pub wafer_auth_secret: String,

    /// TestUnlock token; a 128-bit hex string.
    #[arg(long)]
    pub test_unlock_token: String,

    /// TestExit token; a 128-bit hex string.
    #[arg(long)]
    pub test_exit_token: String,

    /// RMA unlock token; a 128-bit hex string.
    #[arg(long)]
    pub rma_unlock_token: Option<String>,

    /// LC state to transition to from TEST_UNLOCKED*.
    #[arg(long, value_parser = DifLcCtrlState::parse_lc_state_str)]
    target_mission_mode_lc_state: DifLcCtrlState,

    /// Token Encryption public key (RSA) DER file path.
    #[arg(long)]
    token_encrypt_key_der_file: PathBuf,

    /// Pretty-print the provisioning data output.
    #[arg(long, default_value = "false")]
    pretty: bool,
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
    #[arg(long, value_parser = humantime::parse_duration, default_value = "20s")]
    timeout: Duration,

    /// Name of the SPI interface to connect to the OTTF console.
    #[arg(long, default_value = "BOOTSTRAP")]
    console_spi: String,

    /// Owner's firmware string indicating successful start up.
    #[arg(long)]
    owner_success_text: Option<String>,

    /// UJSON payload logging.
    #[arg(long)]
    log_ujson_payloads: bool,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let mut ujson_payloads = UjsonPayloads {
        dut_in: IndexMap::<String, String>::new(),
    };
    let mut response = PersonalizeResponse::default();

    // We call the below functions, instead of calling `opts.init.init_target()` since we do not
    // want to perform bootstrap yet.
    let transport = backend::create(&opts.init.backend_opts)?;
    transport.apply_default_configuration(None)?;
    let spi = transport.spi(&opts.console_spi)?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None)?;
    InitializeTest::print_result(
        "load_bitstream",
        opts.init.load_bitstream.init(&transport).map(|_| None),
    )?;

    // Parse and format tokens.
    let wafer_auth_secret =
        hex_string_to_u8_arrayvec::<32>(opts.provisioning_data.wafer_auth_secret.as_str())?;
    let _test_unlock_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_unlock_token.as_str())?;
    let _test_exit_token =
        hex_string_to_u32_arrayvec::<4>(opts.provisioning_data.test_exit_token.as_str())?;
    let rma_unlock_token = if let Some(token) = &opts.provisioning_data.rma_unlock_token {
        hex_string_to_u32_arrayvec::<4>(token.as_str())?
    } else {
        random_token::<4>()?
    };
    let token_encrypt_key =
        load_rsa_public_key(&opts.provisioning_data.token_encrypt_key_der_file)?;
    let encrypted_rma_unlock_token = encrypt_token(&token_encrypt_key, &rma_unlock_token)?;
    response.rma_unlock_token = Base64::encode_string(&encrypted_rma_unlock_token);
    log::info!("Encrypted rma_unlock_token = {}", response.rma_unlock_token);

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
    let dice_ca_key_id = hex_string_to_u8_arrayvec::<20>(ca_cfgs["dice"].key_id.as_str())?;
    let ext_ca_key_id = if let Some(ext) = ca_cfgs.get("ext") {
        hex_string_to_u8_arrayvec::<20>(ext.key_id.as_str())?
    } else {
        ArrayVec::<u8, 20>::new()
    };
    let _perso_certgen_inputs = ManufCertgenInputs {
        dice_auth_key_key_id: dice_ca_key_id.clone(),
        ext_auth_key_key_id: ext_ca_key_id.clone(),
    };

    // Only run test unlock operation if we are in a locked LC state.
    response.lc_state.initial = read_lc_state(&transport, &opts.init.jtag_params)?;
    match response.lc_state.initial {
        DifLcCtrlState::TestLocked0
        | DifLcCtrlState::TestLocked1
        | DifLcCtrlState::TestLocked2
        | DifLcCtrlState::TestLocked3
        | DifLcCtrlState::TestLocked4
        | DifLcCtrlState::TestLocked5
        | DifLcCtrlState::TestLocked6 => {
            let t0 = Instant::now();
            test_unlock(&transport, &opts.init.jtag_params, &_test_unlock_token)?;
            response.stats.log_elapsed_time("test-unlock", t0);
        }
        _ => {
            log::info!("Skipping test unlock operation. Device is already unlocked.");
        }
    };

    // Only run the SRAM individualize program in a test unlocked state. If we have transitioned to
    // a mission state already, then we can skip this step.
    response.lc_state.unlocked = read_lc_state(&transport, &opts.init.jtag_params)?;
    match response.lc_state.unlocked {
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
            // Run FT individualize.
            response.lc_state.individualize = Some(response.lc_state.unlocked);
            let t0 = Instant::now();
            run_sram_ft_individualize(
                &transport,
                &opts.init.jtag_params,
                &opts.sram_program,
                opts.timeout,
            )?;
            response.stats.log_elapsed_time("ft-individualize", t0);

            // Perform test exit.
            let t0 = Instant::now();
            test_exit(
                &transport,
                &opts.init.jtag_params,
                &_test_exit_token,
                opts.provisioning_data.target_mission_mode_lc_state,
            )?;
            response.lc_state.mission_mode =
                Some(opts.provisioning_data.target_mission_mode_lc_state);
            response.stats.log_elapsed_time("test-exit", t0);
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
        &wafer_auth_secret,
        &rma_unlock_token,
        ca_cfgs,
        ca_keys,
        &_perso_certgen_inputs,
        opts.second_bootstrap,
        &spi_console_device,
        &mut ujson_payloads,
        opts.timeout,
        &mut response,
    )?;

    check_slot_b_boot_up(
        &transport,
        opts.timeout,
        &mut response,
        opts.owner_success_text,
    )?;
    log::info!("Provisioning Done");

    // Extract final device ID.
    let mut final_device_id = read_device_id(&transport, &opts.init.jtag_params)?;

    // Convert final device ID to a big-endian string.
    final_device_id.reverse();
    response.device_id = final_device_id
        .iter()
        .map(|v| format!("{v:08X}"))
        .collect::<Vec<String>>()
        .join("");

    // Log JSON data to console.
    let doc = if opts.provisioning_data.pretty {
        serde_json::to_string_pretty(&response)?
    } else {
        serde_json::to_string(&response)?
    };
    println!("PROVISIONING_DATA: {doc}");

    // Log UJSON payloads.
    if opts.log_ujson_payloads {
        println!();
        println!("UJSON Payloads:");
        for (name, payload) in ujson_payloads.dut_in.into_iter() {
            print!("{:}: ", name);
            for byte in payload.clone().into_bytes() {
                print!("{:02x}", byte);
            }
            println!();
        }
        println!();
    }

    Ok(())
}
