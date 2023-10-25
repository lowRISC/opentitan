// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use clap::Parser;
use std::time::Duration;
use anyhow::Result;
use arrayvec::ArrayVec;
use std::fs;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::aes_commands::{
    AesSubcommand,
    CryptotestAesMode,
    CryptotestAesData,
    CryptotestAesPadding,
    CryptotestAesOperation,
    CryptotestAesOutput,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    aes_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct AesTestCase {
    algorithm: String,
    operation: String,
    key_len: usize,
    mode: String,
    padding: String,
    key: Vec<u8>,
    iv: Option<Vec<u8>>,
    ciphertext: Vec<u8>,
    plaintext: Vec<u8>,
}

const AES_CMD_MAX_MSG_BYTES: usize = 64;
const AES_CMD_MAX_KEY_BYTES: usize = 256 / 8;
const AES_BLOCK_BYTES: usize = 128 / 8;

fn run_aes_testcase(test_case: &AesTestCase, opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;

    assert_eq!(test_case.algorithm.as_str(), "aes");
    CryptotestCommand::Aes.send(&*uart)?;
    AesSubcommand::AesBlock.send(&*uart)?;

    match test_case.mode.as_str() {
        "cbc" => CryptotestAesMode::Cbc.send(&*uart)?,
        "cfb128" => CryptotestAesMode::Cfb.send(&*uart)?,
        "ecb" => CryptotestAesMode::Ecb.send(&*uart)?,
        "ofb" => CryptotestAesMode::Ofb.send(&*uart)?,
        _ => panic!("Invalid AES mode"),
    }
    match test_case.operation.as_str() {
        "encrypt" => CryptotestAesOperation::Encrypt.send(&*uart)?,
        "decrypt" => CryptotestAesOperation::Decrypt.send(&*uart)?,
        _ => panic!("Invalid AES operation"),
    }
    match test_case.padding.as_str() {
        "null" => CryptotestAesPadding::Null.send(&*uart)?,
        "pkcs7" => CryptotestAesPadding::Pkcs7.send(&*uart)?,
        "iso9797m2" => CryptotestAesPadding::Iso9797M2.send(&*uart)?,
        _ => panic!("Invalid AES padding scheme"),
    }

    let mut iv: ArrayVec<u8, AES_BLOCK_BYTES>;
    match &test_case.iv {
        Some(iv_val) => {
            iv = ArrayVec::new();
            iv.try_extend_from_slice(iv_val)?
        },
        None => iv = ArrayVec::from([0; AES_BLOCK_BYTES]),
    }

    let mut key: ArrayVec<u8, AES_CMD_MAX_KEY_BYTES> = ArrayVec::new();
    key.try_extend_from_slice(&test_case.key)?;

    // Configure input and output based on operation
    let input_len;
    let mut input: ArrayVec<u8, AES_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    let expected_output;
    match test_case.operation.as_str() {
        "encrypt" => {
            input.try_extend_from_slice(&test_case.plaintext)?;
            input_len = test_case.plaintext.len();
            expected_output = &test_case.ciphertext;
        },
        "decrypt" => {
            input.try_extend_from_slice(&test_case.ciphertext)?;
            input_len = test_case.ciphertext.len();
            expected_output = &test_case.plaintext;
        },
        _ => panic!("Invalid AES operation"),
    }

    CryptotestAesData {
        key,
        key_length: test_case.key_len / 8,
        iv,
        input,
        input_len,
    }.send(&*uart)?;

    let aes_output = CryptotestAesOutput::recv(&*uart, opts.timeout, false)?;
    assert_eq!(aes_output.output[0..input_len], expected_output[0..input_len]);
    Ok(())
}

fn test_aes(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let test_vector_files = &opts.aes_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let aes_tests: Vec<AesTestCase> = serde_json::from_str(&raw_json)?;

        for aes_test in &aes_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_aes_testcase(aes_test, opts, transport)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_aes, &opts, &transport);
    Ok(())
}
