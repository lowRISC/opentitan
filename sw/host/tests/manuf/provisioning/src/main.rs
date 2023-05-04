// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use aes::cipher::{generic_array::GenericArray, BlockDecrypt, KeyInit};
use aes::Aes256Dec;
use anyhow::Result;
use elliptic_curve::ecdh::diffie_hellman;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::{PublicKey, SecretKey};
use p256::NistP256;
use structopt::StructOpt;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::UartRecv;
use opentitanlib::uart::console::UartConsole;

mod provisioning_data;
use provisioning_data::ManufProvisioning;

#[derive(Debug, StructOpt)]
struct Opts {
    #[structopt(flatten)]
    init: InitializeTest,

    #[structopt(
        long, parse(try_from_str=humantime::parse_duration),
        default_value = "600s",
        help = "Console receive timeout",
    )]
    timeout: Duration,

    #[structopt(long, help = "HSM generated ECDH private key DER file.")]
    hsm_ecdh_sk: PathBuf,
}

fn provisioning(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    // Get UART, set flow control, and wait for for test to start running.
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    // Wait for exported data to be transimitted over the console.
    let export_data = ManufProvisioning::recv(&*uart, opts.timeout, false)?;

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
    let mut plaintext = GenericArray::from_mut_slice(ciphertext.as_mut_slice());

    // Decrypt the RMA unlock token, and convert it to a fixed array of 32-bit words.
    let aes_ecb_cipher = Aes256Dec::new(&aes_key);
    aes_ecb_cipher.decrypt_block(&mut plaintext);
    let mut rma_unlock_token = [0u32; 4];
    for (i, word) in rma_unlock_token.iter_mut().enumerate() {
        *word = u32::from_le_bytes(plaintext[(i * 4)..((i * 4) + 4)].try_into().unwrap());
    }
    log::info!("Decrypted Token: {:#x?}", rma_unlock_token);

    // TODO(#17393): Try to issue an LC transition to RMA to verify unlock token.

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::from_args();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(provisioning, &opts, &transport);
    Ok(())
}
