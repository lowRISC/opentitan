// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use ecdsa::SignatureWithOid;
use ecdsa::{ECDSA_SHA256_OID, ECDSA_SHA384_OID, ECDSA_SHA512_OID};
use num_bigint_dig::BigInt;
use num_traits::Num;
use p256::ecdsa::signature::Verifier;
use p256::elliptic_curve::scalar::ScalarPrimitive as ScalarPrimitiveP256;
use p256::pkcs8::ObjectIdentifier;
use p256::U256;
use p384::elliptic_curve::scalar::ScalarPrimitive as ScalarPrimitiveP384;
use p384::U384;
use serde::Deserialize;
use sha2::digest::generic_array::GenericArray;
use sha2::{Digest, Sha256, Sha384, Sha512};
use std::fs;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::ecdsa_commands::{
    CryptotestEcdsaCoordinate, CryptotestEcdsaCurve, CryptotestEcdsaHashAlg,
    CryptotestEcdsaMessage, CryptotestEcdsaOperation, CryptotestEcdsaPrivateKey,
    CryptotestEcdsaSignature, CryptotestEcdsaVerifyOutput,
};

use opentitanlib::app::TransportWrapper;
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
    ecdsa_json: Vec<String>,
}

fn scalar_zero() -> String {
    String::from("00")
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
    #[serde(default = "scalar_zero")]
    r: String,
    #[serde(default = "scalar_zero")]
    s: String,
    #[serde(default)]
    d: String,
    result: bool,
}

const ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256: usize = 32;
const ECDSA_CMD_MAX_COORDINATE_BYTES_P256: usize = 32;
const ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384: usize = 48;
const ECDSA_CMD_MAX_COORDINATE_BYTES_P384: usize = 48;

// These values were generated randomly for testing purposes.
// Each value must be less than the modulus for its respective curve.
const RANDOM_MASK_P256: &str = "9665cc1c4e9e15354e3fc319ca7de255f2122dc3c16da15e6a83ce1d7a912df0";
const RANDOM_MASK_P384: &str = "e183091e94141f38b570747cec9e2f11da33a9ec7dbcb71187953db7b4e4e3358b020247f2fbcbcb4bf004d2e815f176";

fn p256_verify_signature(
    message: &[u8],
    qx: &mut Vec<u8>,
    qy: &mut Vec<u8>,
    r: &[u8],
    s: &[u8],
    hash_oid: ObjectIdentifier,
) -> bool {
    // Convert qx and qy to big-endian (resize to full length beforehand in case there are leading
    // zero(es))
    qx.resize(ECDSA_CMD_MAX_COORDINATE_BYTES_P256, 0u8);
    qy.resize(ECDSA_CMD_MAX_COORDINATE_BYTES_P256, 0u8);
    qx.reverse();
    qy.reverse();
    // Zero-fill the remaining space for the public key parameters, because
    // p256 requires an exact size
    // Verify the signature with the public key
    p256::ecdsa::VerifyingKey::from_encoded_point(&p256::EncodedPoint::from_affine_coordinates(
        &GenericArray::from(
            <[u8; ECDSA_CMD_MAX_COORDINATE_BYTES_P256]>::try_from(qx.as_slice()).unwrap(),
        ),
        &GenericArray::from(
            <[u8; ECDSA_CMD_MAX_COORDINATE_BYTES_P256]>::try_from(qy.as_slice()).unwrap(),
        ),
        // Don't compress the public key (purely for speed, since we only use
        // it internally)
        false,
    ))
    .expect("Qx and Qy did not form a valid public key")
    .verify(
        message,
        &SignatureWithOid::new(
            p256::ecdsa::Signature::from_scalars(
                GenericArray::from(
                    <[u8; ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256]>::try_from(r).unwrap(),
                ),
                GenericArray::from(
                    <[u8; ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P256]>::try_from(s).unwrap(),
                ),
            )
            .expect("Invalid signature format"),
            hash_oid,
        )
        .expect("Invalid signature format"),
    )
    .is_ok()
}

fn p384_verify_signature(
    message: &[u8],
    qx: &mut Vec<u8>,
    qy: &mut Vec<u8>,
    r: &[u8],
    s: &[u8],
    hash_oid: ObjectIdentifier,
) -> bool {
    // Convert qx and qy to big-endian (resize to full length beforehand in case there are leading
    // zero(es))
    qx.resize(ECDSA_CMD_MAX_COORDINATE_BYTES_P384, 0u8);
    qy.resize(ECDSA_CMD_MAX_COORDINATE_BYTES_P384, 0u8);
    qx.reverse();
    qy.reverse();
    // Zero-fill the remaining space for the public key parameters, because
    // p384 requires an exact size
    // Verify the signature with the public key
    p384::ecdsa::VerifyingKey::from_encoded_point(&p384::EncodedPoint::from_affine_coordinates(
        &GenericArray::from(
            <[u8; ECDSA_CMD_MAX_COORDINATE_BYTES_P384]>::try_from(qx.as_slice()).unwrap(),
        ),
        &GenericArray::from(
            <[u8; ECDSA_CMD_MAX_COORDINATE_BYTES_P384]>::try_from(qy.as_slice()).unwrap(),
        ),
        // Don't compress the public key (purely for speed, since we only use
        // it internally)
        false,
    ))
    .expect("Qx and Qy did not form a valid public key")
    .verify(
        message,
        &SignatureWithOid::new(
            p384::ecdsa::Signature::from_scalars(
                GenericArray::from(
                    <[u8; ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384]>::try_from(r).unwrap(),
                ),
                GenericArray::from(
                    <[u8; ECDSA_CMD_MAX_SIGNATURE_SCALAR_BYTES_P384]>::try_from(s).unwrap(),
                ),
            )
            .expect("Invalid signature format"),
            hash_oid,
        )
        .expect("Invalid signature format"),
    )
    .is_ok()
}

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
    let mut qx: Vec<u8> = BigInt::from_str_radix(&test_case.qx, 16)
        .unwrap()
        .to_bytes_le()
        .1;
    let mut qy: Vec<u8> = BigInt::from_str_radix(&test_case.qy, 16)
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
    let (hash_alg, hash_oid, message_digest): (
        CryptotestEcdsaHashAlg,
        Option<ObjectIdentifier>,
        Vec<u8>,
    ) = match test_case.hash_alg.as_str() {
        "sha-256" => {
            let mut hasher = Sha256::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha256,
                Some(ECDSA_SHA256_OID),
                hasher.finalize().to_vec(),
            )
        }
        "sha-384" => {
            let mut hasher = Sha384::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha384,
                Some(ECDSA_SHA384_OID),
                hasher.finalize().to_vec(),
            )
        }
        "sha-512" => {
            let mut hasher = Sha512::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha512,
                Some(ECDSA_SHA512_OID),
                hasher.finalize().to_vec(),
            )
        }
        "sha3-256" => {
            let mut hasher = sha3::Sha3_256::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha3_256,
                None,
                hasher.finalize().to_vec(),
            )
        }
        "sha3-384" => {
            let mut hasher = sha3::Sha3_384::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha3_384,
                None,
                hasher.finalize().to_vec(),
            )
        }
        "sha3-512" => {
            let mut hasher = sha3::Sha3_512::new();
            hasher.update(test_case.message.as_slice());
            (
                CryptotestEcdsaHashAlg::Sha3_512,
                None,
                hasher.finalize().to_vec(),
            )
        }
        _ => panic!("Invalid ECDSA hash mode"),
    };

    // Determine the curve and check the lengths of the other arguments based on the curve choice.
    // Depending on our choice of curve, calculate the two components of the masked private key.
    let (operation, curve, d0, d1) = match test_case.curve.as_str() {
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
            let (operation, d0, d1) = match test_case.operation.as_str() {
                "sign" => {
                    // Calculate masked private key

                    // Pad private key `d` to 32 bytes
                    let mut padded_d = String::with_capacity(64);
                    for _ in 0..(64 - test_case.d.len()) {
                        padded_d.push('0');
                    }
                    padded_d.push_str(&test_case.d);
                    let d = p256::Scalar::from(
                        ScalarPrimitiveP256::new(U256::from_be_hex(&padded_d)).unwrap(),
                    );
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
                        CryptotestEcdsaOperation::Sign,
                        d0_bytes.to_vec(),
                        d1_bytes.to_vec(),
                    )
                }
                "verify" => (CryptotestEcdsaOperation::Verify, vec![], vec![]),
                _ => panic!("Unsupported ECDSA operation: {}", test_case.operation),
            };
            (operation, CryptotestEcdsaCurve::P256, d0, d1)
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
            let (operation, d0, d1) = match test_case.operation.as_str() {
                "sign" => {
                    // Calculate masked private key

                    // Pad private key `d` to 48 bytes
                    let mut padded_d = String::with_capacity(96);
                    for _ in 0..(96 - test_case.d.len()) {
                        padded_d.push('0');
                    }
                    padded_d.push_str(&test_case.d);
                    let d = p384::Scalar::from(
                        ScalarPrimitiveP384::new(U384::from_be_hex(&padded_d)).unwrap(),
                    );
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
                        CryptotestEcdsaOperation::Sign,
                        d0_bytes.to_vec(),
                        d1_bytes.to_vec(),
                    )
                }
                "verify" => (CryptotestEcdsaOperation::Verify, vec![], vec![]),
                _ => panic!("Unsupported ECDSA operation: {}", test_case.operation),
            };
            (operation, CryptotestEcdsaCurve::P384, d0, d1)
        }
        _ => panic!("Invalid ECDSA curve name"),
    };

    // Send everything
    CryptotestCommand::Ecdsa.send(&*uart)?;
    operation.send(&*uart)?;
    hash_alg.send(&*uart)?;
    curve.send(&*uart)?;

    // Size of `input` is determined at compile-time by type inference
    let mut input = ArrayVec::new();
    // Fill the buffer until we run out of bytes, truncating the rightmost bytes if we have too
    // many
    let msg_len = message_digest.len();
    let mut message_digest_iter = message_digest.iter();
    while !input.is_full() {
        input.push(*message_digest_iter.next().unwrap_or(&0u8));
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

    CryptotestEcdsaPrivateKey {
        d0: ArrayVec::try_from(d0.as_slice()).unwrap(),
        d0_len: d0.len(),
        d1: ArrayVec::try_from(d1.as_slice()).unwrap(),
        d1_len: d1.len(),
        unmasked_len: d0.len(),
    }
    .send(&*uart)?;
    let success = match operation {
        CryptotestEcdsaOperation::Sign => {
            let mut output_signature = CryptotestEcdsaSignature::recv(&*uart, opts.timeout, false)?;
            // Truncate signature values to correct size for curve and convert to big-endian
            output_signature.r.truncate(output_signature.r_len);
            output_signature.s.truncate(output_signature.s_len);
            output_signature.r.reverse();
            output_signature.s.reverse();
            match test_case.curve.as_str() {
                "p256" => p256_verify_signature(
                    &test_case.message,
                    &mut qx,
                    &mut qy,
                    &output_signature.r,
                    &output_signature.s,
                    hash_oid.expect("Unsupported hash algorithm for Sign verification"),
                ),
                "p384" => p384_verify_signature(
                    &test_case.message,
                    &mut qx,
                    &mut qy,
                    &output_signature.r,
                    &output_signature.s,
                    hash_oid.expect("Unsupported hash algorithm for Sign verification"),
                ),
                &_ => panic!("Unsupported ECC curve"),
            }
        }
        CryptotestEcdsaOperation::Verify => {
            let ecdsa_output = CryptotestEcdsaVerifyOutput::recv(&*uart, opts.timeout, false)?;
            match ecdsa_output {
                CryptotestEcdsaVerifyOutput::Success => true,
                CryptotestEcdsaVerifyOutput::Failure => false,
                CryptotestEcdsaVerifyOutput::IntValue(i) => {
                    panic!("Invalid ECDSA verify result: {}", i)
                }
            }
        }
        CryptotestEcdsaOperation::IntValue(_) => {
            unreachable!("Should be caught above")
        }
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
