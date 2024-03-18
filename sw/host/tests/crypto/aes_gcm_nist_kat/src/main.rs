// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::aes_gcm_commands::{
    CryptotestAesGcmOperation, CryptotestAesGcmData, CryptotestAesGcmOutput,
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
    aes_gcm_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct AesGcmTestCase {
    vendor: String,
    test_case_id: usize,
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
const AES_GCM_CMD_MAX_KEY_BYTES: usize = 32;
const AES_GCM_CMD_MAX_IV_BYTES: usize = 128;
const AES_GCM_CMD_MAX_AAD_BYTES: usize = 90;
const AES_GCM_CMD_MAX_TAG_BYTES: usize = 16;

fn run_aes_gcm_testcase(
    test_case: &AesGcmTestCase,
    opts: &Opts,
    transport: &TransportWrapper,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, mode: {}, operation: {}, test case: {}",
        test_case.vendor,
        test_case.mode,
        test_case.operation,
        test_case.test_case_id
    );
    let uart = transport.uart("console")?;

    CryptotestCommand::AesGcm.send(&*uart)?;

    assert!(
        test_case.key_len <= AES_GCM_CMD_MAX_KEY_BYTES,
        "Key too long for device firmware configuration (got = {}, max = {})",
        test_case.key_len,
        AES_GCM_CMD_MAX_KEY_BYTES,
    );
    assert!(
        test_case.plaintext.len() <= AES_GCM_CMD_MAX_MSG_BYTES,
        "Plaintext too long for device firmware configuration (got = {}, max = {})",
        test_case.plaintext.len(),
        AES_GCM_CMD_MAX_MSG_BYTES,
    );
    assert!(
        test_case.ciphertext.len() <= AES_GCM_CMD_MAX_MSG_BYTES,
        "Ciphertext too long for device firmware configuration (got = {}, max = {})",
        test_case.ciphertext.len(),
        AES_GCM_CMD_MAX_MSG_BYTES,
    );
    assert!(
        test_case.iv.len() <= AES_GCM_CMD_MAX_IV_BYTES,
        "IV too long for device firmware configuration (got = {}, max = {})",
        test_case.iv.len(),
        AES_GCM_CMD_MAX_IV_BYTES,
    );
    assert!(
        test_case.aad.len() <= AES_GCM_CMD_MAX_AAD_BYTES,
        "AAD too long for device firmware configuration (got = {}, max = {})",
        test_case.aad.len(),
        AES_GCM_CMD_MAX_AAD_BYTES,
    );
    assert!(
        test_case.tag.len() <= AES_GCM_CMD_MAX_TAG_BYTES,
        "Tag too long for device firmware configuration (got = {}, max = {})",
        test_case.tag.len(),
        AES_GCM_CMD_MAX_TAG_BYTES,
    );

    // Send operation type
    match test_case.operation.as_str() {
        "encrypt" => CryptotestAesGcmOperation::Encrypt,
        "decrypt" => CryptotestAesGcmOperation::Decrypt,
        _ => panic!("Unsupported operation type"),
    }
    .send(&*uart)?;

    // Set input data
    let input_data = if test_case.operation.as_str() == "encrypt" {&test_case.plaintext} else {&test_case.ciphertext};

    // Send data
    CryptotestAesGcmData {
        key: ArrayVec::try_from(test_case.key.as_slice()).unwrap(),
        key_length: test_case.key.len(),
        iv: ArrayVec::try_from(test_case.iv.as_slice()).unwrap(),
        iv_length: test_case.iv.len(),
        aad: ArrayVec::try_from(test_case.aad.as_slice()).unwrap(),
        aad_length: test_case.aad.len(),
        tag: ArrayVec::try_from(test_case.tag.as_slice()).unwrap(),
        tag_length: test_case.tag.len(),
        input: ArrayVec::try_from(input_data.as_slice()).unwrap(),
        input_length: input_data.len(),
    }
    .send(&*uart)?;

    // Get output
    let gcm_output = CryptotestAesGcmOutput::recv(&*uart, opts.timeout, false)?;

    let mut failed = false;
    vec![("oneshot", gcm_output.oneshot_output),
         ("stepwise", gcm_output.stepwise_output)]
    .into_iter()
    .for_each(|(mode, output)|{
        let target_output = if test_case.operation.as_str() == "encrypt" { &test_case.ciphertext } else { &test_case.plaintext };
        let success = if target_output.len() > gcm_output.output_length {
            // If we got a shorter digest back then the test asks for, we
            // can't accept the digest, even if the beginning bytes match.
            false
        } else {
            // Some test cases only specify the beginning bytes of the
            // expected digest, so we only check up to what the test
            // specifies.
            target_output[..] == output[..target_output.len()]
        };
        if test_case.result != success {
            log::info!(
                "FAILED {} test #{} in {} mode: expected = {}, actual = {}",
                test_case.operation,
                test_case.test_case_id,
                mode,
                test_case.result,
                success
            );
            failed = true;
        }
    });
    if failed {
        *fail_counter += 1;
    }
    Ok(())
}

fn test_aes_gcm(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.aes_gcm_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let aes_gcm_tests: Vec<AesGcmTestCase> = serde_json::from_str(&raw_json)?;

        for aes_gcm_test in &aes_gcm_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_aes_gcm_testcase(aes_gcm_test, opts, transport, &mut fail_counter)?;
        }
    }
    assert_eq!(
        0, fail_counter,
        "Failed {} out of {} tests.",
        fail_counter, test_counter
    );
    Ok(())
}


fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_aes_gcm, &opts, &transport);
    Ok(())
}
