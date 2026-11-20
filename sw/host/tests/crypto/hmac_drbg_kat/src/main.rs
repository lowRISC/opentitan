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
use cryptotest_commands::hmac_drbg_commands::{
    CryptotestHmacDrbgInput, CryptotestHmacDrbgMode, CryptotestHmacDrbgOutput,
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
    drbg_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct HmacDrbgTestCase {
    vendor: String,
    test_case_id: usize,
    mode: String,
    entropy: Vec<u8>,
    nonce: Vec<u8>,
    personalization_string: Vec<u8>,
    reseed: bool,
    #[serde(default)]
    reseed_entropy: Vec<u8>,
    #[serde(default)]
    reseed_additional_input: Vec<u8>,
    additional_input_1: Vec<u8>,
    additional_input_2: Vec<u8>,
    output: Vec<u8>,
    result: bool,
}

fn run_hmac_drbg_testcase(
    test_case: &HmacDrbgTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );

    CryptotestCommand::HmacDrbg.send(spi_console)?;

    match test_case.mode.as_str() {
        "SHA-256" => CryptotestHmacDrbgMode::Sha256.send(spi_console)?,
        "SHA-384" => CryptotestHmacDrbgMode::Sha384.send(spi_console)?,
        "SHA-512" => CryptotestHmacDrbgMode::Sha512.send(spi_console)?,
        _ => panic!("Invalid HMAC DRBG mode"),
    };

    // Send everything
    CryptotestHmacDrbgInput {
        entropy: ArrayVec::try_from(test_case.entropy.as_slice()).unwrap(),
        entropy_len: test_case.entropy.len(),
        nonce: ArrayVec::try_from(test_case.nonce.as_slice()).unwrap(),
        nonce_len: test_case.nonce.len(),
        personalization_string: ArrayVec::try_from(test_case.personalization_string.as_slice())
            .unwrap(),
        personalization_string_len: test_case.personalization_string.len(),
        reseed: if test_case.reseed { 1 } else { 0 },
        reseed_entropy: ArrayVec::try_from(test_case.reseed_entropy.as_slice()).unwrap(),
        reseed_entropy_len: test_case.reseed_entropy.len(),
        reseed_additional_input: ArrayVec::try_from(test_case.reseed_additional_input.as_slice())
            .unwrap(),
        reseed_additional_input_len: test_case.reseed_additional_input.len(),
        additional_input_1: ArrayVec::try_from(test_case.additional_input_1.as_slice()).unwrap(),
        additional_input_1_len: test_case.additional_input_1.len(),
        additional_input_2: ArrayVec::try_from(test_case.additional_input_2.as_slice()).unwrap(),
        additional_input_2_len: test_case.additional_input_2.len(),
        output_len: test_case.output.len(),
    }
    .send(spi_console)?;

    // Get output
    let drbg_output = CryptotestHmacDrbgOutput::recv(spi_console, opts.timeout, false, false)?;
    if drbg_output.output_len != test_case.output.len() {
        panic!(
            "Output length: expected = {} actual = {}",
            test_case.output.len(),
            drbg_output.output_len
        );
    }
    let output = Vec::from(&drbg_output.output[..drbg_output.output_len]);
    let success = test_case.output == output;
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

fn test_hmac_drbg(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None, /*ignore_frame_num=*/ false)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

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
    let test_vector_files = &opts.drbg_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let hmac_drbg_tests: Vec<HmacDrbgTestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run
        let stride = min(skip_stride, hmac_drbg_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for hmac_drbg_test in &hmac_drbg_tests {
            test_counter += 1;

            if (hmac_drbg_test.test_case_id % stride) != offset {
                // Skip test
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_hmac_drbg_testcase(hmac_drbg_test, opts, &spi_console_device, &mut fail_counter)?;
        }
    }
    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 10)?;
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
    execute_test!(test_hmac_drbg, &opts, &transport);
    Ok(())
}
