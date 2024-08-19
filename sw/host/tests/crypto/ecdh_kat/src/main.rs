// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use num_bigint_dig::BigUint;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::ecdh_commands::{
    CryptotestEcdhCoordinate, CryptotestEcdhCurve, CryptotestEcdhDeriveOutput,
    CryptotestEcdhPrivateKey,
};
use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use p256::elliptic_curve::scalar::ScalarPrimitive as ScalarPrimitiveP256;
use p256::U256;
use p384::elliptic_curve::scalar::ScalarPrimitive as ScalarPrimitiveP384;
use p384::U384;

const ECDH_CMD_MAX_COORDINATE_BYTES_P256: usize = 32;
const ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P256: usize = 32;
const ECDH_CMD_MAX_COORDINATE_BYTES_P384: usize = 48;
const ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P384: usize = 48;

// These values were generated randomly for testing purposes.
// Each value must be less than the value n for its respective curve.
const RANDOM_MASK_P256: &str = "37c9e5b8e9e24402f2ec25a2eec87c1c531d67e38c18876d70aa50dd925265b1";
const RANDOM_MASK_P384: &str = "b80fee36252d2c38350ad1c00803e09c90f4c086e4cfeed78f164b20b100d5d45f16b678a40a64295438bbebc3e29b09";

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    ecdh_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct EcdhTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    curve: String,
    d: Vec<u8>,
    qx: Vec<u8>,
    qy: Vec<u8>,
    z: Vec<u8>,
    result: bool,
}

fn run_ecdh_testcase(
    test_case: &EcdhTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut usize,
    failures: &mut Vec<usize>,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );

    assert_eq!(test_case.algorithm.as_str(), "ecdh");
    // Change byte slice parameters from big endian to little endian
    let mut d = BigUint::from_bytes_be(&test_case.d).to_bytes_le();
    let qx = BigUint::from_bytes_be(&test_case.qx).to_bytes_le();
    let qy = BigUint::from_bytes_be(&test_case.qy).to_bytes_le();

    CryptotestCommand::Ecdh.send(uart)?;

    let (curve, d0, d1) = match test_case.curve.as_str() {
        "p256" => {
            assert!(
                qx.len() <= ECDH_CMD_MAX_COORDINATE_BYTES_P256,
                "ECDH qx value was too long for curve p256 (got: {}, max: {})",
                qx.len(),
                ECDH_CMD_MAX_COORDINATE_BYTES_P256,
            );
            assert!(
                qy.len() <= ECDH_CMD_MAX_COORDINATE_BYTES_P256,
                "ECDH qy value was too long for curve p256 (got: {}, max: {})",
                qy.len(),
                ECDH_CMD_MAX_COORDINATE_BYTES_P256,
            );
            assert!(
                d.len() <= ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P256,
                "ECDH private key was too long for curve p256 (got: {}, max: {})",
                d.len(),
                ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P256,
            );
            // U256 is picky about having the full byte slice, so extend `d` to be the right size
            d.resize(32, 0u8);

            // Calculate masked private key
            let d = p256::Scalar::from(ScalarPrimitiveP256::new(U256::from_le_slice(&d)).unwrap());
            let d0 = p256::Scalar::from(
                ScalarPrimitiveP256::new(U256::from_be_hex(RANDOM_MASK_P256)).unwrap(),
            );
            // Automatically performs subtraction modulo the order (modulus) of P-256
            let d1 = d - d0;
            // Get big-endian encodings
            let mut d0_bytes = d0.to_bytes();
            let mut d1_bytes = d1.to_bytes();
            // Reverse to get little-endian encodings
            d0_bytes.reverse();
            d1_bytes.reverse();
            (
                CryptotestEcdhCurve::P256,
                d0_bytes.to_vec(),
                d1_bytes.to_vec(),
            )
        }
        "p384" => {
            assert!(
                qx.len() <= ECDH_CMD_MAX_COORDINATE_BYTES_P384,
                "ECDH qx value was too long for curve p384 (got: {}, max: {})",
                qx.len(),
                ECDH_CMD_MAX_COORDINATE_BYTES_P384,
            );
            assert!(
                qy.len() <= ECDH_CMD_MAX_COORDINATE_BYTES_P384,
                "ECDH qy value was too long for curve p384 (got: {}, max: {})",
                qy.len(),
                ECDH_CMD_MAX_COORDINATE_BYTES_P384,
            );
            assert!(
                d.len() <= ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P384,
                "ECDH private key was too long for curve p384 (got: {}, max: {})",
                d.len(),
                ECDH_CMD_MAX_PRIVATE_KEY_BYTES_P384,
            );
            // U384 is picky about having the full byte slice, so extend `d` to be the right size
            d.resize(48, 0u8);

            // Calculate masked private key
            let d = p384::Scalar::from(ScalarPrimitiveP384::new(U384::from_le_slice(&d)).unwrap());
            let d0 = p384::Scalar::from(
                ScalarPrimitiveP384::new(U384::from_be_hex(RANDOM_MASK_P384)).unwrap(),
            );
            // Automatically performs subtraction modulo the order (modulus) of P-384
            let d1 = d - d0;
            // Get big-endian encodings
            let mut d0_bytes = d0.to_bytes();
            let mut d1_bytes = d1.to_bytes();
            // Reverse to get little-endian encodings
            d0_bytes.reverse();
            d1_bytes.reverse();
            (
                CryptotestEcdhCurve::P384,
                d0_bytes.to_vec(),
                d1_bytes.to_vec(),
            )
        }
        _ => panic!("Invalid ECDH curve name"),
    };

    curve.send(uart)?;

    // Sizes were checked already, so we can unwrap() transformations
    // to `ArrayVec`s.  We can inline the `ArrayVec` initialization
    // without providing a type hint because the sizes are enforced by
    // the ujson types.
    CryptotestEcdhPrivateKey {
        d0: ArrayVec::try_from(d0.as_slice()).unwrap(),
        d0_len: d0.len(),
        d1: ArrayVec::try_from(d1.as_slice()).unwrap(),
        d1_len: d1.len(),
    }
    .send(uart)?;

    CryptotestEcdhCoordinate {
        coordinate: ArrayVec::try_from(qx.as_slice()).unwrap(),
        coordinate_len: qx.len(),
    }
    .send(uart)?;

    CryptotestEcdhCoordinate {
        coordinate: ArrayVec::try_from(qy.as_slice()).unwrap(),
        coordinate_len: qy.len(),
    }
    .send(uart)?;

    let ecdh_output = CryptotestEcdhDeriveOutput::recv(uart, opts.timeout, false)?;
    let out_len = ecdh_output.shared_secret_len;
    if out_len > ecdh_output.shared_secret.len() {
        panic!("ECDH returned shared secret was too long for device firmware configuration.");
    }
    // Convert expected value to little-endian
    let mut z = test_case.z.clone();
    z.reverse();
    let success = ecdh_output.ok != 0 && z == ecdh_output.shared_secret[..out_len];
    if success != test_case.result {
        *fail_counter += 1;
        log::info!(
            "FAILED test #{}: expected = {}, actual = {}",
            test_case.test_case_id,
            test_case.result,
            success
        );
        failures.push(test_case.test_case_id);
    }
    Ok(())
}

fn test_ecdh(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0usize;
    let mut failures = vec![];
    let test_vector_files = &opts.ecdh_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let ecdh_tests: Vec<EcdhTestCase> = serde_json::from_str(&raw_json)?;

        for ecdh_test in &ecdh_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_ecdh_testcase(ecdh_test, opts, &*uart, &mut fail_counter, &mut failures)?;
        }
    }
    assert_eq!(
        0, fail_counter,
        "Failed {} out of {} tests. Failed tests: {:?}",
        fail_counter, test_counter, failures,
    );
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_ecdh, &opts, &transport);
    Ok(())
}
