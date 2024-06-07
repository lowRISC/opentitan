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
use cryptotest_commands::hash_commands::{
    CryptotestHashAlgorithm, CryptotestHashMessage, CryptotestHashOutput,
    CryptotestHashShakeDigestLength,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
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
    hash_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct HashTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    message: Vec<u8>,
    // Customization string used for cSHAKE only
    #[serde(default)]
    customization_string: Vec<u8>,
    digest: Vec<u8>,
    result: bool,
}

const HASH_CMD_MAX_MESSAGE_BYTES: usize = 17068;
const HASH_CMD_MAX_CUSTOMIZATION_STRING_BYTES: usize = 16;

fn run_hash_testcase(
    test_case: &HashTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, algorithm: {}, test case: {}",
        test_case.vendor,
        test_case.algorithm,
        test_case.test_case_id
    );

    CryptotestCommand::Hash.send(uart)?;

    assert!(
        test_case.message.len() <= HASH_CMD_MAX_MESSAGE_BYTES,
        "Message too long for device firmware configuration (got = {}, max = {})",
        test_case.message.len(),
        HASH_CMD_MAX_MESSAGE_BYTES,
    );
    assert!(
        test_case.customization_string.len() <= HASH_CMD_MAX_CUSTOMIZATION_STRING_BYTES,
        "Customization string too long for device firmware configuration (got = {}, max = {})",
        test_case.customization_string.len(),
        HASH_CMD_MAX_CUSTOMIZATION_STRING_BYTES,
    );

    // Send algorithm type
    match test_case.algorithm.as_str() {
        "sha-256" => CryptotestHashAlgorithm::Sha256,
        "sha-384" => CryptotestHashAlgorithm::Sha384,
        "sha-512" => CryptotestHashAlgorithm::Sha512,
        "sha3-224" => CryptotestHashAlgorithm::Sha3_224,
        "sha3-256" => CryptotestHashAlgorithm::Sha3_256,
        "sha3-384" => CryptotestHashAlgorithm::Sha3_384,
        "sha3-512" => CryptotestHashAlgorithm::Sha3_512,
        "shake-128" => CryptotestHashAlgorithm::Shake128,
        "shake-256" => CryptotestHashAlgorithm::Shake256,
        "cshake-128" => CryptotestHashAlgorithm::Cshake128,
        "cshake-256" => CryptotestHashAlgorithm::Cshake256,
        _ => panic!("Unsupported hash algorithm"),
    }
    .send(uart)?;

    // Send required digest size for SHAKE tests (this value is
    // ignored for SHA2/3)
    CryptotestHashShakeDigestLength {
        length: test_case.digest.len(),
    }
    .send(uart)?;

    // Send hash preimage
    CryptotestHashMessage {
        message: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
        message_len: test_case.message.len(),
        customization_string: ArrayVec::try_from(test_case.customization_string.as_slice())
            .unwrap(),
        customization_string_len: test_case.customization_string.len(),
    }
    .send(uart)?;

    // Get hash output
    let hash_output = CryptotestHashOutput::recv(uart, opts.timeout, false)?;
    // Stepwise hashing is currently supported by SHA2 only.
    let mut failed = false;
    match test_case.algorithm.as_str() {
        "sha-256" | "sha-384" | "sha-512" => {
            vec![
                ("oneshot", hash_output.oneshot_digest),
                ("stepwise", hash_output.stepwise_digest),
            ]
        }
        _ => vec![("oneshot", hash_output.oneshot_digest)],
    }
    .into_iter()
    .for_each(|(mode, digest)| {
        let success = if test_case.digest.len() > hash_output.digest_len {
            // If we got a shorter digest back then the test asks for, we
            // can't accept the digest, even if the beginning bytes match.
            false
        } else {
            // Some test cases only specify the beginning bytes of the
            // expected digest, so we only check up to what the test
            // specifies.
            test_case.digest[..] == digest[..test_case.digest.len()]
        };
        if test_case.result != success {
            log::info!(
                "FAILED {} test #{} in {} mode: expected = {}, actual = {}",
                test_case.algorithm,
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

fn test_hash(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.hash_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let hash_tests: Vec<HashTestCase> = serde_json::from_str(&raw_json)?;

        for hash_test in &hash_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_hash_testcase(hash_test, opts, &*uart, &mut fail_counter)?;
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
    execute_test!(test_hash, &opts, &transport);
    Ok(())
}
