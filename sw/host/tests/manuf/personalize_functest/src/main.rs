// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

use aes::cipher::{generic_array::GenericArray, BlockDecrypt, KeyInit};
use aes::Aes256Dec;
use anyhow::Result;
use arrayvec::ArrayVec;
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
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;

mod provisioning_data;
use provisioning_data::{EccP256PublicKey, WrappedRmaUnlockToken};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "600s")]
    timeout: Duration,

    /// Host (HSM) generated ECC (P256) private key DER file.
    #[arg(long)]
    host_ecc_sk: PathBuf,
}

fn rma_unlock_token_export(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Load host (HSM) generated ECC keys.
    let host_sk = SecretKey::<NistP256>::read_pkcs8_der_file(&opts.host_ecc_sk)?;
    let host_pk = PublicKey::<NistP256>::from_secret_scalar(&host_sk.to_nonzero_scalar());

    // Format host generated ECC public key to inject it into the device.
    let host_pk_sec1_bytes = host_pk.to_sec1_bytes();
    let num_coord_bytes: usize = (host_pk_sec1_bytes.len() - 1) / 2;
    let mut host_pk_x = host_pk_sec1_bytes.as_ref()[1..num_coord_bytes + 1]
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<ArrayVec<u32, 8>>();
    let mut host_pk_y = host_pk_sec1_bytes.as_ref()[num_coord_bytes + 1..]
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<ArrayVec<u32, 8>>();
    host_pk_x.reverse();
    host_pk_y.reverse();
    let host_pk = EccP256PublicKey {
        x: host_pk_x,
        y: host_pk_y,
    };

    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;

    // Wait for the program to complete SECRET1 configuration and apply a ROM
    // bootstrap operation. This is needed because the flash scrambling key
    // may cause the flash contents to be garbled after locking the SECRET1
    // partition.
    let _ = UartConsole::wait_for(&*uart, r"Provisioning OTP SECRET1 Done ...", opts.timeout)?;
    uart.clear_rx_buffer()?;
    transport.pin_strapping("ROM_BOOTSTRAP")?.apply()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(opts.init.bootstrap.options.reset_delay, true)?;
    opts.init.bootstrap.init(transport)?;

    let _ = UartConsole::wait_for(
        &*uart,
        r"Ready to receive host ECC pubkey ...",
        opts.timeout,
    )?;

    // Send the host ECC public key to the device over the console.
    host_pk.send(&*uart)?;

    // Wait for output data to be transimitted over the console.
    let _ = UartConsole::wait_for(&*uart, r"Exporting RMA unlock token ...", opts.timeout)?;
    let wrapped_rma_token = WrappedRmaUnlockToken::recv(&*uart, opts.timeout, false)?;
    log::info!("{:x?}", wrapped_rma_token);

    // Load device-generated EC public key.
    let mut device_pk_sec1_bytes = Vec::new();
    for key_word in &wrapped_rma_token.device_pk.y {
        device_pk_sec1_bytes.extend(&key_word.to_le_bytes());
    }
    for key_word in &wrapped_rma_token.device_pk.x {
        device_pk_sec1_bytes.extend(&key_word.to_le_bytes());
    }
    device_pk_sec1_bytes.push(0x04); // This indicates the EC public key is not compressed.
    device_pk_sec1_bytes.reverse();
    let device_pk = PublicKey::<NistP256>::from_sec1_bytes(&device_pk_sec1_bytes)?;

    // Peform ECDH to generate shared secret (AES) key.
    let ecdh_shared_secret = diffie_hellman(host_sk.to_nonzero_scalar(), device_pk.as_affine());
    let mut aes_key_bytes = Vec::from(ecdh_shared_secret.raw_secret_bytes().as_slice());
    aes_key_bytes.reverse();
    let aes_key = GenericArray::from_slice(aes_key_bytes.as_slice());

    // Load encrypted RMA unlock token into a GenericArray.
    let mut ciphertext = Vec::new();
    for ciphertext_word in wrapped_rma_token.data {
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
    let mut jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;

    // Check the current LC state is Dev or Prod.
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(
        &mut *jtag,
        Duration::from_secs(3),
        LcCtrlStatus::INITIALIZED,
    )?;
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
        jtag,
        DifLcCtrlState::Rma,
        Some(rma_unlock_token),
        /*use_external_clk=*/ false,
        opts.init.bootstrap.options.reset_delay,
        Some(JtagTap::LcTap),
    )?;

    jtag = opts
        .init
        .jtag_params
        .create(transport)?
        .connect(JtagTap::LcTap)?;

    // Check the LC state is RMA.
    // We must wait for the lc_ctrl to initialize before the LC state is exposed.
    wait_for_status(
        &mut *jtag,
        Duration::from_secs(3),
        LcCtrlStatus::INITIALIZED,
    )?;
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
