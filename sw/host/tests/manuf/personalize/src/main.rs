// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

use aes::cipher::{generic_array::GenericArray, BlockDecrypt, KeyInit};
use aes::Aes256Dec;
use anyhow::Result;
use clap::Parser;
use elliptic_curve::ecdh::diffie_hellman;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::{PublicKey, SecretKey};
use p256::NistP256;

use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg, LcCtrlStatus};
use opentitanlib::execute_test;
use opentitanlib::io::jtag::JtagTap;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::{trigger_lc_transition, wait_for_status};
use opentitanlib::test_utils::rpc::UartRecv;
use opentitanlib::uart::console::UartConsole;

mod provisioning_data;
use provisioning_data::ManufPersoDataOut;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// HSM generated ECDH private key DER file.
    #[arg(long)]
    hsm_ecdh_sk: PathBuf,
}

fn rma_unlock_token_export(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Reset the chip, select the LC TAP, we will connect to it later.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;

    // Get UART, set flow control, and wait for for test to start running.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(
        &*uart,
        r"Personalization complete. Checking status ...",
        opts.timeout,
    )?;

    // Wait for exported data to be transimitted over the console.
    let export_data = ManufPersoDataOut::recv(&*uart, opts.timeout, false)?;
    log::info!("{:x?}", export_data);

    // Load HSM-generated EC private key.
    let hsm_sk = SecretKey::<NistP256>::read_pkcs8_der_file(&opts.hsm_ecdh_sk)?;

    // Load device-generated EC public key.
    let mut device_pk_sec1_bytes = Vec::new();
    for key_word in &export_data.wrapped_rma_unlock_token.ecc_pk_device_y {
        device_pk_sec1_bytes.extend(&key_word.to_le_bytes());
    }
    for key_word in &export_data.wrapped_rma_unlock_token.ecc_pk_device_x {
        device_pk_sec1_bytes.extend(&key_word.to_le_bytes());
    }
    device_pk_sec1_bytes.push(0x04); // This indicates the EC public key is not compressed.
    device_pk_sec1_bytes.reverse();
    let device_pk = PublicKey::<NistP256>::from_sec1_bytes(&device_pk_sec1_bytes)?;

    // Peform ECDH to generate shared secret (AES) key.
    let ecdh_shared_secret = diffie_hellman(hsm_sk.to_nonzero_scalar(), device_pk.as_affine());
    let mut aes_key_bytes = Vec::from(ecdh_shared_secret.raw_secret_bytes().as_slice());
    aes_key_bytes.reverse();
    let aes_key = GenericArray::from_slice(aes_key_bytes.as_slice());

    // Load encrypted RMA unlock token into a GenericArray.
    let mut ciphertext = Vec::new();
    for ciphertext_word in export_data.wrapped_rma_unlock_token.data {
        ciphertext.extend(&ciphertext_word.to_le_bytes());
    }
    let plaintext = GenericArray::from_mut_slice(ciphertext.as_mut_slice());

    // Decrypt the RMA unlock token, and convert it to a fixed array of 32-bit words.
    let aes_ecb_cipher = Aes256Dec::new(aes_key);
    aes_ecb_cipher.decrypt_block(plaintext);
    let mut rma_unlock_token = [0u32; 4];
    for (i, word) in rma_unlock_token.iter_mut().enumerate() {
        *word = u32::from_le_bytes(plaintext[(i * 4)..((i * 4) + 4)].try_into().unwrap());
    }

    // Connect to JTAG LC TAP.
    let jtag = opts.init.jtag_params.create(transport)?;
    jtag.connect(JtagTap::LcTap)?;

    // Check the current LC state is Dev or Prod.
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(&jtag, Duration::from_secs(3), LcCtrlStatus::INITIALIZED)?;
    let valid_lc_states = HashSet::from([
        DifLcCtrlState::Dev.redundant_encoding(),
        DifLcCtrlState::Prod.redundant_encoding(),
    ]);
    let current_lc_state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert!(
        valid_lc_states.contains(&current_lc_state),
        "Invalid initial LC state (must be in Dev or Prod to test transition to RMA).",
    );

    // Issue an LC transition to RMA to verify unlock token.
    // The device program will spin when it detects the RMA state so we can safely
    // reconnect to the LC TAP after the transition without risking the chip resetting.
    trigger_lc_transition(
        transport,
        jtag.clone(),
        DifLcCtrlState::Rma,
        Some(rma_unlock_token),
        /*use_external_clk=*/ false,
        opts.init.bootstrap.options.reset_delay,
        Some(JtagTap::LcTap),
    )?;

    // Check the LC state is RMA.
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(&jtag, Duration::from_secs(3), LcCtrlStatus::INITIALIZED)?;
    assert_eq!(
        jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?,
        DifLcCtrlState::Rma.redundant_encoding(),
        "Did not transition to RMA.",
    );

    jtag.disconnect()?;

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;

    execute_test!(rma_unlock_token_export, &opts, &transport);

    Ok(())
}
