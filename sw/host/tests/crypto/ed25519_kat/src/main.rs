// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use serde::Deserialize;
use std::cmp::min;
use std::fs;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::ed25519_commands::{
    CryptotestEd25519Message, CryptotestEd25519Operation, CryptotestEd25519PrivateKey,
    CryptotestEd25519PublicKey, CryptotestEd25519SignMode, CryptotestEd25519Signature,
    CryptotestEd25519VerifyOutput,
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
    // If skip_stride is set to 0, all the tests are run.
    #[arg(long, default_value_t = 0usize)]
    skip_stride: usize,

    // Seed value for random number generator.
    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, num_args = 1..)]
    ed25519_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct Ed25519TestCase {
    algorithm: String,
    operation: String,
    message: Vec<u8>,
    public_key: Vec<u8>,
    #[serde(default)]
    private_key: Vec<u8>,
    signature: Vec<u8>,
    result: bool,
}

// Fixed sizes defined by the Ed25519 algorithm.
const ED25519_PUBLIC_KEY_BYTES: usize = 32;
const ED25519_PRIVATE_KEY_SEED_BYTES: usize = 32;
const ED25519_SIGNATURE_BYTES: usize = 64;

// Fixed mask for additive sharing of the Ed25519 private key seed.
// seed = d0 + d1 (mod 2^256). Generated randomly for testing purposes.
const RANDOM_MASK_ED25519: [u8; ED25519_PRIVATE_KEY_SEED_BYTES] = [
    0x7e, 0x3f, 0x8a, 0x5c, 0x12, 0xd6, 0xb4, 0x90, 0xaf, 0x7e, 0x3d, 0x81, 0xc4, 0xb2, 0x5f, 0x98,
    0xe0, 0xa1, 0xd7, 0x3c, 0x5b, 0x2e, 0x8f, 0x4a, 0x96, 0xd0, 0xc7, 0x1b, 0x38, 0xe4, 0xf2, 0x5a,
];

fn run_ed25519_testcase(
    test_case: &Ed25519TestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    failures: &mut Vec<String>,
    test_counter: usize,
) -> Result<()> {
    log::info!("test case: {}", test_counter);
    assert_eq!(test_case.algorithm.as_str(), "ed25519");

    let operation = match test_case.operation.as_str() {
        "verify" => CryptotestEd25519Operation::Verify,
        "sign" => CryptotestEd25519Operation::Sign,
        _ => panic!("Unsupported Ed25519 operation: {}", test_case.operation),
    };

    assert_eq!(
        test_case.public_key.len(),
        ED25519_PUBLIC_KEY_BYTES,
        "Ed25519 public key must be exactly {} bytes (got {})",
        ED25519_PUBLIC_KEY_BYTES,
        test_case.public_key.len(),
    );

    // Wycheproof Ed25519 test vectors use pure EdDSA.
    let sign_mode = CryptotestEd25519SignMode::Eddsa;

    CryptotestCommand::Ed25519.send(spi_console)?;
    operation.send(spi_console)?;
    sign_mode.send(spi_console)?;

    CryptotestEd25519Message {
        input: ArrayVec::try_from(test_case.message.as_slice())
            .expect("Ed25519 message was too large for device firmware configuration."),
        input_len: test_case.message.len(),
    }
    .send(spi_console)?;

    // For verify: send the actual signature (R component reversed for device byte
    // ordering). For sign: the firmware ignores this field; send an empty buffer.
    let mut signature_bytes = test_case.signature.clone();
    if matches!(operation, CryptotestEd25519Operation::Verify)
        && signature_bytes.len() >= ED25519_SIGNATURE_BYTES / 2
    {
        signature_bytes[..ED25519_SIGNATURE_BYTES / 2].reverse();
    }
    CryptotestEd25519Signature {
        signature: ArrayVec::try_from(signature_bytes.as_slice())
            .expect("Ed25519 signature had unexpected length."),
        signature_len: signature_bytes.len(),
    }
    .send(spi_console)?;

    // Public key is used by verify; firmware derives it from the private key for sign.
    CryptotestEd25519PublicKey {
        public_key: ArrayVec::try_from(test_case.public_key.as_slice())
            .expect("Ed25519 public key had unexpected length."),
        public_key_len: test_case.public_key.len(),
    }
    .send(spi_console)?;

    // For sign: additively mask the private key seed (seed = d0 + d1 mod 2^256).
    // For verify: the firmware ignores the private key; send empty shares.
    let (d0_bytes, d1_bytes): (Vec<u8>, Vec<u8>) =
        if matches!(operation, CryptotestEd25519Operation::Sign) {
            assert_eq!(
                test_case.private_key.len(),
                ED25519_PRIVATE_KEY_SEED_BYTES,
                "Ed25519 private key must be exactly {} bytes (got {})",
                ED25519_PRIVATE_KEY_SEED_BYTES,
                test_case.private_key.len(),
            );
            let seed = &test_case.private_key;
            let d0 = RANDOM_MASK_ED25519;
            let mut d1 = [0u8; ED25519_PRIVATE_KEY_SEED_BYTES];
            let mut borrow: i16 = 0;
            for i in 0..ED25519_PRIVATE_KEY_SEED_BYTES {
                let diff = seed[i] as i16 - d0[i] as i16 - borrow;
                d1[i] = diff as u8;
                borrow = if diff < 0 { 1 } else { 0 };
            }
            (d0.to_vec(), d1.to_vec())
        } else {
            (vec![], vec![])
        };
    CryptotestEd25519PrivateKey {
        d0: ArrayVec::try_from(d0_bytes.as_slice()).unwrap(),
        d0_len: d0_bytes.len(),
        d1: ArrayVec::try_from(d1_bytes.as_slice()).unwrap(),
        d1_len: d1_bytes.len(),
    }
    .send(spi_console)?;

    let success = match operation {
        CryptotestEd25519Operation::Verify | CryptotestEd25519Operation::Sign => {
            let output =
                CryptotestEd25519VerifyOutput::recv(spi_console, opts.timeout, false, false)?;
            match output {
                CryptotestEd25519VerifyOutput::Success => true,
                CryptotestEd25519VerifyOutput::Failure => false,
                CryptotestEd25519VerifyOutput::IntValue(i) => {
                    panic!("Invalid Ed25519 result: {}", i)
                }
            }
        }
        CryptotestEd25519Operation::IntValue(_) => {
            unreachable!("Should be caught above")
        }
    };

    if test_case.result != success {
        log::info!(
            "FAILED test #{}: expected = {}, actual = {}",
            test_counter,
            test_case.result,
            success
        );
        failures.push(format!(
            "{} {} #{}",
            test_case.algorithm, test_case.operation, test_counter
        ));
    }
    Ok(())
}

fn test_ed25519(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(
        &*spi,
        None,
        /*ignore_frame_num=*/ false,
        Some(opts.init.backend_opts.interface.as_str()),
    )?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    let seed = opts.seed.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(opts.skip_stride)
    {
        Some(offset) => (opts.skip_stride, offset),
        // If skip_stride is 0, run all tests.
        None => (1usize, 0usize),
    };

    let mut test_counter = 0usize;
    let mut failures = vec![];
    let test_vector_files = &opts.ed25519_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let ed25519_tests: Vec<Ed25519TestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run.
        let stride = min(skip_stride, ed25519_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for (i, ed25519_test) in ed25519_tests.iter().enumerate() {
            test_counter += 1;

            if (i % stride) != offset {
                // Skip test.
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_ed25519_testcase(
                ed25519_test,
                opts,
                &spi_console_device,
                &mut failures,
                test_counter,
            )?;
        }
    }
    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 10)?;
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
    execute_test!(test_ed25519, &opts, &transport);
    Ok(())
}
