// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::rsa_commands::{
    CryptotestRsaDecrypt, CryptotestRsaDecryptResp, CryptotestRsaEncrypt, CryptotestRsaEncryptResp,
    CryptotestRsaVerify, CryptotestRsaVerifyResp, RsaSubcommand,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    rsa_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct RsaTestCase {
    algorithm: String,
    operation: String,
    padding: String,
    security_level: usize,
    hash_alg: String,
    message: Vec<u8>,
    n: Vec<u8>,
    e: u32,
    result: bool,
    #[serde(default)]
    signature: Vec<u8>,
    #[serde(default)]
    d: Vec<u8>,
    #[serde(default)]
    label: Vec<u8>,
    #[serde(default)]
    ciphertext: Vec<u8>,
}

fn run_rsa_testcase(
    test_case: &RsaTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    assert_eq!(test_case.algorithm.as_str(), "rsa");

    // Configure hashing.
    let hashing = match test_case.hash_alg.as_str() {
        "sha-256" => 0,
        "sha-384" => 1,
        "sha-512" => 2,
        "sha3-256" => 3,
        "sha3-384" => 4,
        "sha3-512" => 5,
        "shake-128" => 6,
        "shake-256" => 7,
        _ => panic!("Invalid hashing mode"),
    };

    // Configure padding mode.
    let padding = match test_case.padding.as_str() {
        "pkcs1_1.5" => 0,
        "pss" => 1,
        "oaep" => 2,
        _ => panic!("Invalid padding mode"),
    };

    // Convert the inputs into the expected format for the CL.
    let n: Vec<_> = test_case.n.iter().copied().rev().collect();

    CryptotestCommand::Rsa.send(spi_console)?;
    let _operation = &match test_case.operation.as_str() {
        "verify" => {
            // Send RsaVerify command.
            RsaSubcommand::RsaVerify.send(spi_console)?;

            // Convert the inputs into the expected format for the CL.
            let signature: Vec<_> = test_case.signature.iter().copied().rev().collect();

            // Assemble the input.
            CryptotestRsaVerify {
                msg: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
                msg_len: test_case.message.len(),
                e: test_case.e,
                n: ArrayVec::try_from(n.as_slice()).unwrap(),
                security_level: test_case.security_level,
                sig: ArrayVec::try_from(signature.as_slice()).unwrap(),
                sig_len: test_case.signature.len(),
                hashing,
                padding,
            }
            .send(spi_console)?;

            // Get and evaluate the response.
            let rsa_verify_resp = CryptotestRsaVerifyResp::recv(spi_console, opts.timeout, false)?;
            assert_eq!(rsa_verify_resp.result, test_case.result);
        }
        "decrypt" => {
            // Send RsaDecrypt command.
            RsaSubcommand::RsaDecrypt.send(spi_console)?;

            // Convert the inputs into the expected format for the CL.
            let d: Vec<_> = test_case.d.iter().copied().rev().collect();
            let ctx: Vec<_> = test_case.ciphertext.iter().copied().rev().collect();

            // Assemble the input.
            CryptotestRsaDecrypt {
                ciphertext: ArrayVec::try_from(ctx.as_slice()).unwrap(),
                ciphertext_len: test_case.ciphertext.len(),
                e: test_case.e,
                d: ArrayVec::try_from(d.as_slice()).unwrap(),
                n: ArrayVec::try_from(n.as_slice()).unwrap(),
                security_level: test_case.security_level,
                label: ArrayVec::try_from(test_case.label.as_slice()).unwrap(),
                label_len: test_case.label.len(),
                hashing,
                padding,
            }
            .send(spi_console)?;

            // Get and evaluate the response.
            let rsa_decrypt_resp =
                CryptotestRsaDecryptResp::recv(spi_console, opts.timeout, false)?;
            // Check if the decryption was successful.
            assert_eq!(rsa_decrypt_resp.result, test_case.result);

            if test_case.result {
                // Only check plaintext if the response is valid.
                assert_eq!(
                    rsa_decrypt_resp.plaintext[0..test_case.message.len()],
                    test_case.message[0..test_case.message.len()]
                );
            }
        }
        "encrypt" => {
            // Send RsaEncrypt command.
            RsaSubcommand::RsaEncrypt.send(spi_console)?;

            // Convert the inputs into the expected format for the CL.
            let ptx: Vec<_> = test_case.message.iter().copied().rev().collect();

            // Assemble the input.
            CryptotestRsaEncrypt {
                plaintext: ArrayVec::try_from(ptx.as_slice()).unwrap(),
                plaintext_len: test_case.message.len(),
                e: test_case.e,
                n: ArrayVec::try_from(n.as_slice()).unwrap(),
                security_level: test_case.security_level,
                label: ArrayVec::try_from(test_case.label.as_slice()).unwrap(),
                label_len: test_case.label.len(),
                hashing,
                padding,
            }
            .send(spi_console)?;

            // Get and evaluate the response.
            let rsa_encrypt_resp =
                CryptotestRsaEncryptResp::recv(spi_console, opts.timeout, false)?;
            // Check if the encryption was successful.
            assert_eq!(rsa_encrypt_resp.result, test_case.result);

            // Use the received ciphertext, decrypt it, and compare it to the
            // plaintext in the test vector.
            if test_case.result {
                // Decrypt it again and check if the plaintext matches.
                // Send RsaDecrypt command.
                CryptotestCommand::Rsa.send(spi_console)?;
                RsaSubcommand::RsaDecrypt.send(spi_console)?;

                // Convert the inputs into the expected format for the CL.
                let d: Vec<_> = test_case.d.iter().copied().rev().collect();
                let ctx: Vec<_> =
                    Vec::from(&rsa_encrypt_resp.ciphertext[..rsa_encrypt_resp.ciphertext_len]);

                // Assemble the input.
                CryptotestRsaDecrypt {
                    ciphertext: ArrayVec::try_from(ctx.as_slice()).unwrap(),
                    ciphertext_len: rsa_encrypt_resp.ciphertext_len,
                    e: test_case.e,
                    d: ArrayVec::try_from(d.as_slice()).unwrap(),
                    n: ArrayVec::try_from(n.as_slice()).unwrap(),
                    security_level: test_case.security_level,
                    label: ArrayVec::try_from(test_case.label.as_slice()).unwrap(),
                    label_len: test_case.label.len(),
                    hashing,
                    padding,
                }
                .send(spi_console)?;

                // Get and evaluate the response.
                let rsa_decrypt_resp =
                    CryptotestRsaDecryptResp::recv(spi_console, opts.timeout, false)?;
                // Check if the decryption was successful.
                assert_eq!(rsa_decrypt_resp.result, test_case.result);

                if test_case.result {
                    // Only check plaintext if the response is valid.
                    assert_eq!(
                        rsa_decrypt_resp.plaintext[0..test_case.message.len()],
                        test_case.message[0..test_case.message.len()]
                    );
                }
            }
        }
        _ => panic!("Invalid operation"),
    };

    Ok(())
}

fn test_rsa(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let test_vector_files = &opts.rsa_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let rsa_tests: Vec<RsaTestCase> = serde_json::from_str(&raw_json)?;

        for rsa_test in &rsa_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_rsa_testcase(rsa_test, opts, &spi_console_device)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_rsa, &opts, &transport);
    Ok(())
}
