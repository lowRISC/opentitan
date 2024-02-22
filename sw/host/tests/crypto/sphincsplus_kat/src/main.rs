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
use cryptotest_commands::sphincsplus_commands::{
    CryptotestSphincsPlusHashAlg, CryptotestSphincsPlusMessage, CryptotestSphincsPlusOperation,
    CryptotestSphincsPlusPublicKey, CryptotestSphincsPlusSignature,
    CryptotestSphincsPlusVerifyOutput,
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
    sphincsplus_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct SphincsPlusTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    operation: String,
    hash_alg: String,
    public: Vec<u8>,
    message: Vec<u8>,
    signature: Vec<u8>,
    result: bool,
}

fn run_sphincsplus_testcase(
    test_case: &SphincsPlusTestCase,
    opts: &Opts,
    transport: &TransportWrapper,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, algorithm: {}, test case: {}",
        test_case.vendor,
        test_case.algorithm,
        test_case.test_case_id
    );
    let uart = transport.uart("console")?;

    CryptotestCommand::SphincsPlus.send(&*uart)?;
    assert_eq!(test_case.algorithm.as_str(), "sphincs+");

    // Send operation
    match test_case.operation.as_str() {
        "verify" => CryptotestSphincsPlusOperation::Verify,
        _ => panic!("Unsupported SPHINCS+ operation"),
    }
    .send(&*uart)?;

    // Send hash algorithm
    match test_case.hash_alg.as_str() {
        "sha-256" => CryptotestSphincsPlusHashAlg::Sha256,
        "shake-256" => CryptotestSphincsPlusHashAlg::Shake256,
        _ => panic!("Unsupported hash algorithm"),
    }
    .send(&*uart)?;

    // Send public key
    CryptotestSphincsPlusPublicKey {
        public: ArrayVec::try_from(test_case.public.as_slice())
            .expect("SPHINCS+ public key was too large for device firmware configuration."),
        public_len: test_case.public.len(),
    }
    .send(&*uart)?;

    // Send message
    CryptotestSphincsPlusMessage {
        message: ArrayVec::try_from(test_case.message.as_slice())
            .expect("SPHINCS+ message was too large for device firmware configuration."),
        message_len: test_case.message.len(),
    }
    .send(&*uart)?;

    // Send signature
    CryptotestSphincsPlusSignature {
        signature: ArrayVec::try_from(test_case.signature.as_slice())
            .expect("SPHINCS+ signature was too large for device firmware configuration."),
        signature_len: test_case.signature.len(),
    }
    .send(&*uart)?;

    // Get verification output
    let success = match CryptotestSphincsPlusVerifyOutput::recv(&*uart, opts.timeout, false)? {
        CryptotestSphincsPlusVerifyOutput::Success => true,
        CryptotestSphincsPlusVerifyOutput::Failure => false,
        CryptotestSphincsPlusVerifyOutput::IntValue(i) => {
            panic!("Invalid SPHINCS+ verify result: {}", i)
        }
    };
    if test_case.result != success {
        log::info!(
            "FAILED test #{}: expected = {}, actual = {}",
            test_case.test_case_id,
            test_case.result,
            success
        );
        *fail_counter += 1;
    }
    Ok(())
}

fn test_sphincsplus(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.sphincsplus_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let sphincsplus_tests: Vec<SphincsPlusTestCase> = serde_json::from_str(&raw_json)?;

        for sphincsplus_test in &sphincsplus_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_sphincsplus_testcase(sphincsplus_test, opts, transport, &mut fail_counter)?;
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
    execute_test!(test_sphincsplus, &opts, &transport);
    Ok(())
}
