// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use openssl::bn::BigNum;
use openssl::encrypt::Decrypter;
use openssl::hash::MessageDigest;
use openssl::pkey::PKey;
use openssl::rsa::{Padding, Rsa, RsaPrivateKeyBuilder};
use openssl::sign::{RsaPssSaltlen, Verifier};
use std::cmp::min;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::rsa_commands::{
    CryptotestRsaDecrypt, CryptotestRsaDecryptResp, CryptotestRsaEncrypt, CryptotestRsaEncryptResp,
    CryptotestRsaKeygenCheck, CryptotestRsaKeygenCheckResp, CryptotestRsaSign,
    CryptotestRsaSignResp, CryptotestRsaVerify, CryptotestRsaVerifyResp, RsaSubcommand,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    // Reduce number of tests that are run by this factor.
    // 1 out of skip_stride tests are run. The ID of the first test to run is
    // (pseudo-)randomly chosen between 0 and skip_stride.
    // If skip_stride is set to 0, all the tests are run
    #[arg(long, default_value_t = 0usize)]
    skip_stride: usize,

    // Seed value for random number generator.
    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, num_args = 1..)]
    rsa_json: Vec<String>,

    // Run RSA keygen functional tests (sign-then-verify and encrypt-then-decrypt
    // round-trips with freshly generated keys).
    #[arg(long, default_value_t = false)]
    run_keygen: bool,
}

#[derive(Debug, Deserialize)]
struct RsaTestCase {
    test_case_id: u32,
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

fn openssl_md(hash_alg: &str) -> MessageDigest {
    match hash_alg {
        "sha-256" => MessageDigest::sha256(),
        "sha-384" => MessageDigest::sha384(),
        "sha-512" => MessageDigest::sha512(),
        "sha3-256" => MessageDigest::sha3_256(),
        "sha3-384" => MessageDigest::sha3_384(),
        "sha3-512" => MessageDigest::sha3_512(),
        _ => panic!("Invalid hashing mode"),
    }
}

fn verify_rsa_signature_on_host(
    n_be: &[u8],
    e: u32,
    padding: &str,
    hash_alg: &str,
    message: &[u8],
    sig_be: &[u8],
) -> Result<bool> {
    let rsa_pub = Rsa::from_public_components(BigNum::from_slice(n_be)?, BigNum::from_u32(e)?)?;
    let pkey = PKey::from_rsa(rsa_pub)?;
    let md = openssl_md(hash_alg);
    let mut verifier = Verifier::new(md, &pkey)?;
    match padding {
        "pkcs1_1.5" => {
            verifier.set_rsa_padding(Padding::PKCS1)?;
        }
        "pss" => {
            verifier.set_rsa_padding(Padding::PKCS1_PSS)?;
            verifier.set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH)?;
            verifier.set_rsa_mgf1_md(md)?;
        }
        _ => panic!("Invalid signing padding mode"),
    }
    verifier.update(message)?;
    Ok(verifier.verify(sig_be)?)
}

fn decrypt_rsa_oaep_on_host(
    n_be: &[u8],
    e: u32,
    d_be: &[u8],
    hash_alg: &str,
    label: &[u8],
    ct_be: &[u8],
) -> Result<Vec<u8>> {
    let rsa_priv = RsaPrivateKeyBuilder::new(
        BigNum::from_slice(n_be)?,
        BigNum::from_u32(e)?,
        BigNum::from_slice(d_be)?,
    )?
    .build();
    let pkey = PKey::from_rsa(rsa_priv)?;
    let md = openssl_md(hash_alg);
    let mut decrypter = Decrypter::new(&pkey)?;
    decrypter.set_rsa_padding(Padding::PKCS1_OAEP)?;
    decrypter.set_rsa_oaep_md(md)?;
    decrypter.set_rsa_mgf1_md(md)?;
    if !label.is_empty() {
        decrypter.set_rsa_oaep_label(label)?;
    }
    let buf_len = decrypter.decrypt_len(ct_be)?;
    let mut decrypted = vec![0u8; buf_len];
    let dec_len = decrypter.decrypt(ct_be, &mut decrypted)?;
    decrypted.truncate(dec_len);
    Ok(decrypted)
}

fn normalize_le_key_bytes(raw_be: &[u8], expected_len: usize) -> Vec<u8> {
    let mut le: Vec<_> = raw_be.iter().copied().rev().collect();
    while le.len() > expected_len {
        assert_eq!(le.pop(), Some(0));
    }
    if le.len() < expected_len {
        le.resize(expected_len, 0);
    }
    le
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
    // n in the wycheproof vectors can start with a leading 0.
    let n_bytes = test_case.security_level / (u8::BITS as usize);
    let n = normalize_le_key_bytes(&test_case.n, n_bytes);
    let n_be: Vec<_> = n.iter().copied().rev().collect();

    if test_case.e == 65537 {
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
                let rsa_verify_resp =
                    CryptotestRsaVerifyResp::recv(spi_console, opts.timeout, false, false)?;
                assert_eq!(rsa_verify_resp.result, test_case.result);
            }
            "sign" => {
                // Send RsaSign command.
                RsaSubcommand::RsaSign.send(spi_console)?;

                // Convert the inputs into the expected format for the CL.
                let d = normalize_le_key_bytes(&test_case.d, n_bytes);

                // Assemble the input.
                CryptotestRsaSign {
                    msg: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
                    msg_len: test_case.message.len(),
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

                // Get the response and convert device little-endian signature to big-endian.
                let rsa_sign_resp =
                    CryptotestRsaSignResp::recv(spi_console, opts.timeout, false, false)?;
                let sig_be: Vec<_> = rsa_sign_resp.signature[..rsa_sign_resp.signature_len]
                    .iter()
                    .copied()
                    .rev()
                    .collect();

                // PKCS#1 v1.5 signing is deterministic; compare against expected signature if present.
                if test_case.padding == "pkcs1_1.5" && !test_case.signature.is_empty() {
                    assert_eq!(sig_be, test_case.signature);
                }

                // Verify the device signature on the host against an independent library.
                let verified = verify_rsa_signature_on_host(
                    &n_be,
                    test_case.e,
                    &test_case.padding,
                    &test_case.hash_alg,
                    &test_case.message,
                    &sig_be,
                )?;
                assert_eq!(verified, test_case.result);
            }
            "decrypt" => {
                // Send RsaDecrypt command.
                RsaSubcommand::RsaDecrypt.send(spi_console)?;

                // Convert the inputs into the expected format for the CL.
                let d = normalize_le_key_bytes(&test_case.d, n_bytes);
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
                    CryptotestRsaDecryptResp::recv(spi_console, opts.timeout, false, false)?;
                // Check if the decryption was successful.
                assert_eq!(rsa_decrypt_resp.result, test_case.result);

                if test_case.result {
                    // Only check plaintext if the response is valid.
                    assert_eq!(rsa_decrypt_resp.plaintext_len, test_case.message.len());
                    assert_eq!(
                        rsa_decrypt_resp.plaintext[0..test_case.message.len()],
                        test_case.message[0..test_case.message.len()]
                    );
                }
            }
            "encrypt" => {
                // Send RsaEncrypt command.
                RsaSubcommand::RsaEncrypt.send(spi_console)?;

                // Plaintext is a raw byte array, not a little-endian integer.
                CryptotestRsaEncrypt {
                    plaintext: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
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
                    CryptotestRsaEncryptResp::recv(spi_console, opts.timeout, false, false)?;
                // Check if the encryption was successful.
                assert_eq!(rsa_encrypt_resp.result, test_case.result);

                // Decrypt the received ciphertext on the host and compare against the plaintext.
                if test_case.result {
                    let d = normalize_le_key_bytes(&test_case.d, n_bytes);
                    let d_be: Vec<_> = d.iter().copied().rev().collect();
                    let ct_be: Vec<_> = rsa_encrypt_resp.ciphertext
                        [..rsa_encrypt_resp.ciphertext_len]
                        .iter()
                        .copied()
                        .rev()
                        .collect();
                    let decrypted = decrypt_rsa_oaep_on_host(
                        &n_be,
                        test_case.e,
                        &d_be,
                        &test_case.hash_alg,
                        &test_case.label,
                        &ct_be,
                    )?;
                    assert_eq!(decrypted, test_case.message);
                }
            }
            _ => panic!("Invalid operation"),
        };
    }

    Ok(())
}

// (security_level_bits, padding, hash_alg) parameter sets for keygen testing.
// All three padding modes are covered for each security level. The message is
// kept short to satisfy the OAEP plaintext bound at the largest hash size.
const KEYGEN_CASES: &[(usize, &str, &str)] = &[
    (2048, "pkcs1_1.5", "sha-256"),
    (2048, "pss", "sha-256"),
    (2048, "oaep", "sha-256"),
    (3072, "pkcs1_1.5", "sha-384"),
    (3072, "pss", "sha-384"),
    (3072, "oaep", "sha-384"),
    (4096, "pkcs1_1.5", "sha-512"),
    (4096, "pss", "sha-512"),
    (4096, "oaep", "sha-512"),
];

const KEYGEN_TEST_MESSAGE: &[u8] = &[
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
];

fn run_rsa_keygen_testcase(
    security_level: usize,
    padding: &str,
    hash_alg: &str,
    spi_console: &SpiConsoleDevice,
    timeout: Duration,
) -> Result<()> {
    let hashing = match hash_alg {
        "sha-256" => 0,
        "sha-384" => 1,
        "sha-512" => 2,
        "sha3-256" => 3,
        "sha3-384" => 4,
        "sha3-512" => 5,
        _ => panic!("Invalid hashing mode"),
    };
    let padding_code = match padding {
        "pkcs1_1.5" => 0,
        "pss" => 1,
        "oaep" => 2,
        _ => panic!("Invalid padding mode"),
    };

    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaKeygenCheck.send(spi_console)?;
    CryptotestRsaKeygenCheck {
        security_level,
        hashing,
        padding: padding_code,
        msg: ArrayVec::try_from(KEYGEN_TEST_MESSAGE).unwrap(),
        msg_len: KEYGEN_TEST_MESSAGE.len(),
    }
    .send(spi_console)?;

    let resp = CryptotestRsaKeygenCheckResp::recv(spi_console, timeout, false, false)?;
    assert!(
        resp.result,
        "RSA keygen round-trip failed for {security_level}-bit {padding} {hash_alg}"
    );
    Ok(())
}

fn test_rsa(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None, /*ignore_frame_num=*/ false)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running ", opts.timeout)?;

    let seed = opts.seed.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    // Create a deterministic RNG from the seed for skipping
    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(opts.skip_stride)
    {
        Some(offset) => (opts.skip_stride, offset),
        // if opts.skip_stride is 0, skip_stride is set to 1 to execute all the tests
        None => (1usize, 0usize),
    };

    let test_vector_files = &opts.rsa_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let rsa_tests: Vec<RsaTestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run
        let stride = min(skip_stride, rsa_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for rsa_test in &rsa_tests {
            if (rsa_test.test_case_id as usize % stride) != offset {
                // Skip test
                continue;
            }

            log::info!("Test counter: {}", rsa_test.test_case_id);
            run_rsa_testcase(rsa_test, opts, &spi_console_device)?;
        }
    }

    if opts.run_keygen {
        for &(security_level, padding, hash_alg) in KEYGEN_CASES {
            log::info!(
                "RSA keygen: {}-bit {} {}",
                security_level,
                padding,
                hash_alg
            );
            run_rsa_keygen_testcase(
                security_level,
                padding,
                hash_alg,
                &spi_console_device,
                opts.timeout,
            )?;
        }
    }

    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 10)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_rsa, &opts, &transport);
    Ok(())
}
