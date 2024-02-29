// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use crypto::{
    digest::Digest,
    sha2::{Sha256, Sha384, Sha512},
    sha3::Sha3,
};
use num_bigint_dig::BigInt;
use num_traits::Num;
use serde::Deserialize;
use std::fs;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::ecdsa_commands::{
    CryptotestEcdsaCoordinate, CryptotestEcdsaCurve, CryptotestEcdsaHashAlg,
    CryptotestEcdsaMessage, CryptotestEcdsaOperation, CryptotestEcdsaSignature,
    CryptotestEcdsaVerifyOutput,
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
    ecdsa_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct EcdsaTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    operation: String,
    curve: String,
    hash_alg: String,
    message: Vec<u8>,
    qx: String,
    qy: String,
    r: String,
    s: String,
    result: bool,
}

const ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256: usize = 32;
const ECDSA_CMD_MAX_COORDINATE_BYTES_P256: usize = 32;
const ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384: usize = 48;
const ECDSA_CMD_MAX_COORDINATE_BYTES_P384: usize = 48;

fn run_ecdsa_testcase(
    test_case: &EcdsaTestCase,
    opts: &Opts,
    transport: &TransportWrapper,
    failures: &mut Vec<String>,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );
    let uart = transport.uart("console")?;
    assert_eq!(test_case.algorithm.as_str(), "ecdsa");
    let qx: Vec<u8> = BigInt::from_str_radix(&test_case.qx, 16)
        .unwrap()
        .to_bytes_le()
        .1;
    let qy: Vec<u8> = BigInt::from_str_radix(&test_case.qy, 16)
        .unwrap()
        .to_bytes_le()
        .1;
    let r: Vec<u8> = BigInt::from_str_radix(&test_case.r, 16)
        .unwrap()
        .to_bytes_le()
        .1;
    let s: Vec<u8> = BigInt::from_str_radix(&test_case.s, 16)
        .unwrap()
        .to_bytes_le()
        .1;

    // Get the hash function and hash the message to get the digest (unfortunately this code is
    // challenging to deduplicate because the `Digest` trait is not object safe).
    let (hash_alg, message_digest): (CryptotestEcdsaHashAlg, Vec<u8>) =
        match test_case.hash_alg.as_str() {
            "sha-256" => {
                let mut hasher = Sha256::new();
                hasher.input(test_case.message.as_slice());
                let mut out = vec![0u8; hasher.output_bytes()];
                hasher.result(&mut out);
                (CryptotestEcdsaHashAlg::Sha256, out)
            }
            "sha-384" => {
                let mut hasher = Sha384::new();
                hasher.input(test_case.message.as_slice());
                let mut out = vec![0u8; hasher.output_bytes()];
                hasher.result(&mut out);
                (CryptotestEcdsaHashAlg::Sha384, out)
            }
            "sha-512" => {
                let mut hasher = Sha512::new();
                hasher.input(test_case.message.as_slice());
                let mut out = vec![0u8; hasher.output_bytes()];
                hasher.result(&mut out);
                (CryptotestEcdsaHashAlg::Sha512, out)
            }
            "sha3-256" => {
                let mut hasher = Sha3::sha3_256();
                hasher.input(test_case.message.as_slice());
                let mut out = vec![0u8; hasher.output_bytes()];
                hasher.result(&mut out);
                (CryptotestEcdsaHashAlg::Sha3_256, out)
            }
            "sha3-512" => {
                let mut hasher = Sha3::sha3_512();
                hasher.input(test_case.message.as_slice());
                let mut out = vec![0u8; hasher.output_bytes()];
                hasher.result(&mut out);
                (CryptotestEcdsaHashAlg::Sha3_512, out)
            }
            _ => panic!("Invalid ECDSA hash mode"),
        };

    // Determine the curve and check the lengths of the other arguments based on the curve choice
    let curve = match test_case.curve.as_str() {
        "p256" => {
            assert!(
                qx.len() <= ECDSA_CMD_MAX_COORDINATE_BYTES_P256,
                "ECDSA qx value was too long for curve p256 (got: {}, max: {})",
                qx.len(),
                ECDSA_CMD_MAX_COORDINATE_BYTES_P256,
            );
            assert!(
                qy.len() <= ECDSA_CMD_MAX_COORDINATE_BYTES_P256,
                "ECDSA qy value was too long for curve p256 (got: {}, max: {})",
                qy.len(),
                ECDSA_CMD_MAX_COORDINATE_BYTES_P256,
            );
            assert!(
                r.len() <= ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256,
                "ECDSA signature value r was too long for curve p256 (got: {}, max: {})",
                r.len(),
                ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256,
            );
            assert!(
                s.len() <= ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256,
                "ECDSA signature value s was too long for curve p256 (got: {}, max: {})",
                s.len(),
                ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256,
            );
            CryptotestEcdsaCurve::P256
        }
        "p384" => {
            assert!(
                qx.len() <= ECDSA_CMD_MAX_COORDINATE_BYTES_P384,
                "ECDSA qx value was too long for curve p384 (got: {}, max: {})",
                qx.len(),
                ECDSA_CMD_MAX_COORDINATE_BYTES_P384,
            );
            assert!(
                qy.len() <= ECDSA_CMD_MAX_COORDINATE_BYTES_P384,
                "ECDSA qy value was too long for curve p384 (got: {}, max: {})",
                qy.len(),
                ECDSA_CMD_MAX_COORDINATE_BYTES_P384,
            );
            assert!(
                r.len() <= ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384,
                "ECDSA signature value r was too long for curve p384 (got: {}, max: {})",
                r.len(),
                ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384,
            );
            assert!(
                s.len() <= ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384,
                "ECDSA signature value s was too long for curve p384 (got: {}, max: {})",
                s.len(),
                ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384,
            );
            CryptotestEcdsaCurve::P384
        }
        _ => panic!("Invalid ECDSA curve name"),
    };

    // Send everything
    CryptotestCommand::Ecdsa.send(&*uart)?;
    match test_case.operation.as_str() {
        "verify" => CryptotestEcdsaOperation::Verify,
        _ => panic!("Invalid ECDSA operation"),
    }
    .send(&*uart)?;
    hash_alg.send(&*uart)?;
    curve.send(&*uart)?;

    // Size of `input` is determined at compile-time by type inference
    let mut input = ArrayVec::new();
    // Fill the buffer until we run out of bytes, truncating the rightmost bytes if we have too
    // many
    let msg_len = message_digest.len();
    let mut message_digest = message_digest.into_iter();
    while !input.is_full() {
        input.push(message_digest.next().unwrap_or(0u8));
    }
    // `unwrap()` operations are safe here because we checked the sizes above.
    let msg = CryptotestEcdsaMessage {
        input,
        input_len: msg_len,
    };
    msg.send(&*uart)?;

    CryptotestEcdsaSignature {
        r: ArrayVec::try_from(r.as_slice()).unwrap(),
        r_len: r.len(),
        s: ArrayVec::try_from(s.as_slice()).unwrap(),
        s_len: s.len(),
    }
    .send(&*uart)?;

    CryptotestEcdsaCoordinate {
        coordinate: ArrayVec::try_from(qx.as_slice()).unwrap(),
        coordinate_len: qx.len(),
    }
    .send(&*uart)?;

    CryptotestEcdsaCoordinate {
        coordinate: ArrayVec::try_from(qy.as_slice()).unwrap(),
        coordinate_len: qy.len(),
    }
    .send(&*uart)?;

    let ecdsa_output = CryptotestEcdsaVerifyOutput::recv(&*uart, opts.timeout, false)?;
    let success = match ecdsa_output {
        CryptotestEcdsaVerifyOutput::Success => true,
        CryptotestEcdsaVerifyOutput::Failure => false,
        CryptotestEcdsaVerifyOutput::IntValue(i) => panic!("Invalid ECDSA verify result: {}", i),
    };
    if test_case.result != success {
        log::info!(
            "FAILED test #{}: expected = {}, actual = {}",
            test_case.test_case_id,
            test_case.result,
            success
        );
        failures.push(format!(
            "{} {} {} {} #{}",
            test_case.vendor,
            test_case.curve,
            test_case.operation,
            test_case.hash_alg,
            test_case.test_case_id
        ));
    }
    Ok(())
}

fn test_ecdsa(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut failures = vec![];
    let test_vector_files = &opts.ecdsa_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let ecdsa_tests: Vec<EcdsaTestCase> = serde_json::from_str(&raw_json)?;

        for ecdsa_test in &ecdsa_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_ecdsa_testcase(ecdsa_test, opts, transport, &mut failures)?;
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
    execute_test!(test_ecdsa, &opts, &transport);
    Ok(())
}
