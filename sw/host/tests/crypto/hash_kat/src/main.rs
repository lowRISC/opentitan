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
use cryptotest_commands::hash_commands::{
    CryptotestHashAlgorithm, CryptotestHashMessage, CryptotestHashOutput,
    CryptotestHashShakeDigestLength,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
#[command(args_override_self = true)]
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
    digest: Vec<u8>,
    result: bool,
}

const HASH_CMD_MAX_MESSAGE_BYTES: usize = 17068;

fn run_hash_testcase(
    test_case: &HashTestCase,
    opts: &Opts,
    transport: &TransportWrapper,
    failures: &mut Vec<String>,
    quiet: bool,
) -> Result<()> {
    log::info!(
        "vendor: {}, algorithm: {}, test case: {}",
        test_case.vendor,
        test_case.algorithm,
        test_case.test_case_id
    );
    let uart = transport.uart("console")?;

    CryptotestCommand::Hash.send(&*uart)?;

    assert!(
        test_case.message.len() <= HASH_CMD_MAX_MESSAGE_BYTES,
        "Message too long for device firmware configuration (got = {}, max = {})",
        test_case.message.len(),
        HASH_CMD_MAX_MESSAGE_BYTES,
    );

    // Send algorithm type
    match test_case.algorithm.as_str() {
        "sha-256" => CryptotestHashAlgorithm::Sha256,
        "sha-384" => CryptotestHashAlgorithm::Sha384,
        "sha-512" => CryptotestHashAlgorithm::Sha512,
        "sha3-256" => CryptotestHashAlgorithm::Sha3_256,
        "sha3-384" => CryptotestHashAlgorithm::Sha3_384,
        "sha3-512" => CryptotestHashAlgorithm::Sha3_512,
        "shake-128" => CryptotestHashAlgorithm::Shake128,
        "shake-256" => CryptotestHashAlgorithm::Shake256,
        _ => panic!("Unsupported hash algorithm"),
    }
    .send(&*uart)?;

    // Send required digest size for SHAKE tests (this value is
    // ignored for SHA2/3)
    CryptotestHashShakeDigestLength {
        length: test_case.digest.len(),
    }
    .send(&*uart)?;

    // Send hash preimage
    CryptotestHashMessage {
        message: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
        message_len: test_case.message.len(),
    }
    .send(&*uart)?;

    // Get hash output
    let hash_output = CryptotestHashOutput::recv(&*uart, opts.timeout, quiet)?;
    // Stepwise hashing is currently supported by SHA2 only.
    let mut failed_oneshot = false;
    let mut failed_stepwise = false;
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
            match mode {
                "oneshot" => {
                    failed_oneshot = true;
                }
                "stepwise" => {
                    failed_stepwise = true;
                }
                _ => unreachable!("Invalid mode value"),
            }
        }
    });
    if failed_oneshot {
        failures.push(format!(
            "{} {} #{} oneshot",
            test_case.vendor, test_case.algorithm, test_case.test_case_id
        ));
    }
    if failed_stepwise {
        failures.push(format!(
            "{} {} #{} stepwise",
            test_case.vendor, test_case.algorithm, test_case.test_case_id
        ));
    }
    Ok(())
}

fn test_hash(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut failures = vec![];
    let test_vector_files = &opts.hash_json;
    // A filter level of `Error` indicates we're running in CI, so we don't want to print the
    // output of every UART recv().
    let quiet = opts.init.logging == log::LevelFilter::Error;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let hash_tests: Vec<HashTestCase> = serde_json::from_str(&raw_json)?;

        for hash_test in &hash_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_hash_testcase(hash_test, opts, transport, &mut failures, quiet)?;
        }
    }
    assert_eq!(
        0,
        failures.len(),
        "Failed {} out of {} tests. Failures: {:?}",
        failures.len(),
        test_counter,
        failures
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
