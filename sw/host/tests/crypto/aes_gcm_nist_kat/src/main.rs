// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::aes_gcm_commands::{
    AesGcmSubcommand, CryptotestAesGcmData, CryptotestAesGcmOperation, CryptotestAesGcmOutput,
};
use cryptotest_commands::commands::CryptotestCommand;

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
    aes_gcm_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct AesGcmTestCase {
    mode: String,
    operation: String,
    key_len: usize,
    key: Vec<u8>,
    aad: Vec<u8>,
    iv: Vec<u8>,
    tag: Vec<u8>,
    ciphertext: Vec<u8>,
    plaintext: Vec<u8>,
    result: bool,
}

const AES_GCM_CMD_MAX_MSG_BYTES: usize = 64;
const AES_GCM_CMD_MAX_KEY_BYTES: usize = 256 / 8;
const AES_BLOCK_BYTES: usize = 128 / 8;

fn run_aes_gcm_testcase(
    test_case: &AesGcmTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    assert_eq!(test_case.mode.as_str(), "gcm");
    CryptotestCommand::AesGcm.send(spi_console)?;
    AesGcmSubcommand::AesGcmOp.send(spi_console)?;

    match test_case.operation.as_str() {
        "encrypt" => CryptotestAesGcmOperation::Encrypt.send(spi_console)?,
        "decrypt" => CryptotestAesGcmOperation::Decrypt.send(spi_console)?,
        _ => panic!("Invalid AES-GCM operation"),
    };

    let mut iv: ArrayVec<u8, AES_BLOCK_BYTES> = ArrayVec::new();
    iv.try_extend_from_slice(&test_case.iv)?;

    let mut key: ArrayVec<u8, AES_GCM_CMD_MAX_KEY_BYTES> = ArrayVec::new();
    key.try_extend_from_slice(&test_case.key)?;

    // Configure input and output based on operation
    let input_length;
    let mut input: ArrayVec<u8, AES_GCM_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    let expected_output;
    let expected_tag;
    let expected_tag_check;
    match test_case.operation.as_str() {
        "encrypt" => {
            input.try_extend_from_slice(&test_case.plaintext)?;
            input_length = test_case.plaintext.len();
            expected_output = &test_case.ciphertext;
            expected_tag = &test_case.tag;
            expected_tag_check = test_case.result;
        }
        "decrypt" => {
            input.try_extend_from_slice(&test_case.ciphertext)?;
            input_length = test_case.ciphertext.len();
            expected_output = &test_case.plaintext;
            expected_tag = &test_case.tag;
            expected_tag_check = test_case.result;
        }
        _ => panic!("Invalid AES-GCM operation"),
    }

    CryptotestAesGcmData {
        key,
        key_length: test_case.key_len / 8,
        iv,
        iv_length: test_case.iv.len(),
        input,
        input_length,
        aad: ArrayVec::try_from(test_case.aad.as_slice()).unwrap(),
        aad_length: test_case.aad.len(),
        tag: ArrayVec::try_from(test_case.tag.as_slice()).unwrap(),
        tag_length: test_case.tag.len(),
    }
    .send(spi_console)?;

    let aes_gcm_output = CryptotestAesGcmOutput::recv(spi_console, opts.timeout, false)?;

    // Check if the tag comparison matches.
    assert_eq!(aes_gcm_output.tag_valid, expected_tag_check);

    // Check if the tag output matches.
    assert_eq!(
        aes_gcm_output.tag[0..test_case.tag.len()],
        expected_tag[0..test_case.tag.len()]
    );

    if expected_tag_check {
        // Only check output if the tag is valid as the testvectors don't
        // have an output if the tag is invalid.
        assert_eq!(
            aes_gcm_output.output[0..input_length],
            expected_output[0..input_length]
        );
    }

    Ok(())
}

fn test_aes_gcm(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running ", opts.timeout)?;

    let mut test_counter = 0u32;
    let test_vector_files = &opts.aes_gcm_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let aes_gcm_tests: Vec<AesGcmTestCase> = serde_json::from_str(&raw_json)?;

        for aes_gcm_test in &aes_gcm_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_aes_gcm_testcase(aes_gcm_test, opts, &spi_console_device)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_aes_gcm, &opts, &transport);
    Ok(())
}
