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
use cryptotest_commands::hmac_commands::{
    CryptotestHmacHashAlg, CryptotestHmacKey, CryptotestHmacMessage, CryptotestHmacTag,
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
    hmac_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct HmacTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    hash_alg: String,
    key: Vec<u8>,
    message: Vec<u8>,
    tag: Vec<u8>,
    result: bool,
}

const HMAC_CMD_MAX_MESSAGE_BYTES: usize = 256;
const HMAC_CMD_MAX_KEY_BYTES: usize = 192;

fn run_hmac_testcase(
    test_case: &HmacTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );
    assert_eq!(test_case.algorithm.as_str(), "hmac");
    CryptotestCommand::Hmac.send(spi_console)?;

    assert!(
        test_case.key.len() <= HMAC_CMD_MAX_KEY_BYTES,
        "Key too long for device firmware configuration (got = {}, max = {})",
        test_case.key.len(),
        HMAC_CMD_MAX_KEY_BYTES,
    );
    assert!(
        test_case.message.len() <= HMAC_CMD_MAX_MESSAGE_BYTES,
        "Message too long for device firmware configuration (got = {}, max = {})",
        test_case.message.len(),
        HMAC_CMD_MAX_MESSAGE_BYTES,
    );

    match test_case.hash_alg.as_str() {
        "sha-256" => CryptotestHmacHashAlg::Sha256,
        "sha-384" => CryptotestHmacHashAlg::Sha384,
        "sha-512" => CryptotestHmacHashAlg::Sha512,
        "sha3-256" => CryptotestHmacHashAlg::Sha3_256,
        "sha3-384" => CryptotestHmacHashAlg::Sha3_384,
        "sha3-512" => CryptotestHmacHashAlg::Sha3_512,
        _ => panic!("Unsupported HMAC hash mode"),
    }
    .send(spi_console)?;

    CryptotestHmacKey {
        key: ArrayVec::try_from(test_case.key.as_slice()).unwrap(),
        key_len: test_case.key.len(),
    }
    .send(spi_console)?;

    CryptotestHmacMessage {
        message: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
        message_len: test_case.message.len(),
    }
    .send(spi_console)?;

    let hmac_tag = CryptotestHmacTag::recv(spi_console, opts.timeout, false, false)?;
    let success = if test_case.tag.len() > hmac_tag.tag_len {
        // If we got a shorter tag back then the test asks for, we can't accept the tag, even if
        // the beginning bytes match.
        false
    } else {
        // Some of the NIST test cases only specify the beginning bytes of the expected tag, so we
        // only check up to what the test specifies.
        test_case.tag[..] == hmac_tag.tag[..test_case.tag.len()]
    };
    if test_case.result != success {
        log::info!(
            "FAILED test #{}: expected = {}, actual = {}",
            test_case.test_case_id,
            test_case.result,
            success
        );
    }
    if success != test_case.result {
        *fail_counter += 1;
    }
    Ok(())
}

fn test_hmac(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let test_vector_files = &opts.hmac_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let hmac_tests: Vec<HmacTestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run
        let stride = min(skip_stride, hmac_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for hmac_test in &hmac_tests {
            test_counter += 1;

            if (hmac_test.test_case_id % stride) != offset {
                // Skip test
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_hmac_testcase(hmac_test, opts, &spi_console_device, &mut fail_counter)?;
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
    execute_test!(test_hmac, &opts, &transport);
    Ok(())
}
