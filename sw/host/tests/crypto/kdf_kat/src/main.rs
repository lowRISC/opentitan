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
use cryptotest_commands::kdf_commands::{
    CryptotestKdfAlgorithm, CryptotestKdfContext, CryptotestKdfKey, CryptotestKdfLabel,
    CryptotestKdfMode, CryptotestKdfOutput, CryptotestKdfRequiredOutputLength,
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
    kdf_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct KdfTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    mode: String,
    key: Vec<u8>,
    label: Vec<u8>,
    context: Vec<u8>,
    output: Vec<u8>,
    result: bool,
}

const KDF_CMD_MAX_KEY_BYTES: usize = 192;
const KDF_CMD_MAX_LABEL_BYTES: usize = 192;
const KDF_CMD_MAX_CONTEXT_BYTES: usize = 256;
const KDF_CMD_MAX_OUTPUT_BYTES: usize = 256;

fn run_kdf_testcase(
    test_case: &KdfTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );
    CryptotestCommand::Kdf.send(spi_console)?;

    assert!(
        test_case.key.len() <= KDF_CMD_MAX_KEY_BYTES,
        "Key too long for device firmware configuration (got = {}, max = {})",
        test_case.key.len(),
        KDF_CMD_MAX_KEY_BYTES,
    );
    assert!(
        test_case.label.len() <= KDF_CMD_MAX_LABEL_BYTES,
        "Label too long for device firmware configuration (got = {}, max = {})",
        test_case.label.len(),
        KDF_CMD_MAX_LABEL_BYTES,
    );
    assert!(
        test_case.context.len() <= KDF_CMD_MAX_CONTEXT_BYTES,
        "Context too long for device firmware configuration (got = {}, max = {})",
        test_case.context.len(),
        KDF_CMD_MAX_CONTEXT_BYTES,
    );
    assert!(
        test_case.output.len() <= KDF_CMD_MAX_OUTPUT_BYTES,
        "Output too long for device firmware configuration (got = {}, max = {})",
        test_case.output.len(),
        KDF_CMD_MAX_OUTPUT_BYTES,
    );

    match test_case.algorithm.as_str() {
        "hkdf" => CryptotestKdfAlgorithm::Hkdf,
        "kmac-kdf" => CryptotestKdfAlgorithm::KmacKdf,
        "kdf-ctr" => CryptotestKdfAlgorithm::KdfCtr,
        _ => panic!("Unsupported KDF algorithm: {}", test_case.algorithm),
    }
    .send(spi_console)?;

    match test_case.mode.as_str() {
        "sha-256" => CryptotestKdfMode::Sha256,
        "sha-384" => CryptotestKdfMode::Sha384,
        "sha-512" => CryptotestKdfMode::Sha512,
        "kmac-128" => CryptotestKdfMode::Kmac128,
        "kmac-256" => CryptotestKdfMode::Kmac256,
        _ => panic!("Unsupported KDF mode: {}", test_case.mode),
    }
    .send(spi_console)?;

    CryptotestKdfRequiredOutputLength {
        required_output_length: test_case.output.len(),
    }
    .send(spi_console)?;

    CryptotestKdfKey {
        key: ArrayVec::try_from(test_case.key.as_slice()).unwrap(),
        key_len: test_case.key.len(),
    }
    .send(spi_console)?;

    CryptotestKdfLabel {
        label: ArrayVec::try_from(test_case.label.as_slice()).unwrap(),
        label_len: test_case.label.len(),
    }
    .send(spi_console)?;

    CryptotestKdfContext {
        context: ArrayVec::try_from(test_case.context.as_slice()).unwrap(),
        context_len: test_case.context.len(),
    }
    .send(spi_console)?;

    let kdf_output = CryptotestKdfOutput::recv(spi_console, opts.timeout, false, false)?;
    let success = if test_case.output.len() > kdf_output.output_len {
        false
    } else {
        test_case.output[..] == kdf_output.output[..test_case.output.len()]
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

fn test_kdf(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
        None => (1usize, 0usize),
    };

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.kdf_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let kdf_tests: Vec<KdfTestCase> = serde_json::from_str(&raw_json)?;

        let stride = min(skip_stride, kdf_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for kdf_test in &kdf_tests {
            test_counter += 1;

            if (kdf_test.test_case_id % stride) != offset {
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_kdf_testcase(kdf_test, opts, &spi_console_device, &mut fail_counter)?;
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
    execute_test!(test_kdf, &opts, &transport);
    Ok(())
}
