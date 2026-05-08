// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use std::cmp::min;
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
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, algorithm: {}, test case: {}",
        test_case.vendor,
        test_case.algorithm,
        test_case.test_case_id
    );
    CryptotestCommand::SphincsPlus.send(spi_console)?;
    assert_eq!(test_case.algorithm.as_str(), "sphincs+");

    // Send operation
    match test_case.operation.as_str() {
        "verify" => CryptotestSphincsPlusOperation::Verify,
        _ => panic!("Unsupported SPHINCS+ operation"),
    }
    .send(spi_console)?;

    // Send hash algorithm
    match test_case.hash_alg.as_str() {
        "sha-256" => CryptotestSphincsPlusHashAlg::Sha256,
        "shake-256" => CryptotestSphincsPlusHashAlg::Shake256,
        _ => panic!("Unsupported hash algorithm"),
    }
    .send(spi_console)?;

    // Send public key
    CryptotestSphincsPlusPublicKey {
        public: ArrayVec::try_from(test_case.public.as_slice())
            .expect("SPHINCS+ public key was too large for device firmware configuration."),
        public_len: test_case.public.len(),
    }
    .send(spi_console)?;

    // Send message
    CryptotestSphincsPlusMessage {
        message: ArrayVec::try_from(test_case.message.as_slice())
            .expect("SPHINCS+ message was too large for device firmware configuration."),
        message_len: test_case.message.len(),
    }
    .send(spi_console)?;

    // Send signature
    CryptotestSphincsPlusSignature {
        signature: ArrayVec::try_from(test_case.signature.as_slice())
            .expect("SPHINCS+ signature was too large for device firmware configuration."),
        signature_len: test_case.signature.len(),
    }
    .send(spi_console)?;

    // Get verification output
    let success =
        match CryptotestSphincsPlusVerifyOutput::recv(spi_console, opts.timeout, false, false)? {
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

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.sphincsplus_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let sphincsplus_tests: Vec<SphincsPlusTestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run
        let stride = min(skip_stride, sphincsplus_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for sphincsplus_test in &sphincsplus_tests {
            test_counter += 1;

            if (sphincsplus_test.test_case_id % stride) != offset {
                // Skip test
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_sphincsplus_testcase(
                sphincsplus_test,
                opts,
                &spi_console_device,
                &mut fail_counter,
            )?;
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
