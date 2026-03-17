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

use cryptotest_commands::aes_commands::{
    AesSubcommand, CryptotestAesData, CryptotestAesMode, CryptotestAesOperation,
    CryptotestAesOutput, CryptotestAesPadding,
};
use cryptotest_commands::commands::CryptotestCommand;

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
    aes_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct AesTestCase {
    algorithm: String,
    operation: String,
    key_len: usize,
    mode: String,
    padding: String,
    key: Vec<u8>,
    iv: Option<Vec<u8>>,
    ciphertext: Vec<u8>,
    plaintext: Vec<u8>,
}

const AES_CMD_MAX_MSG_BYTES: usize = 64;
const AES_CMD_MAX_KEY_BYTES: usize = 256 / 8;
const AES_BLOCK_BYTES: usize = 128 / 8;

fn run_aes_testcase(
    test_case: &AesTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    assert_eq!(test_case.algorithm.as_str(), "aes");
    CryptotestCommand::Aes.send(spi_console)?;
    AesSubcommand::AesBlock.send(spi_console)?;

    match test_case.mode.as_str() {
        "cbc" => CryptotestAesMode::Cbc.send(spi_console)?,
        "cfb128" => CryptotestAesMode::Cfb.send(spi_console)?,
        "ecb" => CryptotestAesMode::Ecb.send(spi_console)?,
        "ofb" => CryptotestAesMode::Ofb.send(spi_console)?,
        _ => panic!("Invalid AES mode"),
    };
    match test_case.operation.as_str() {
        "encrypt" => CryptotestAesOperation::Encrypt.send(spi_console)?,
        "decrypt" => CryptotestAesOperation::Decrypt.send(spi_console)?,
        _ => panic!("Invalid AES operation"),
    };
    match test_case.padding.as_str() {
        "null" => CryptotestAesPadding::Null.send(spi_console)?,
        "pkcs7" => CryptotestAesPadding::Pkcs7.send(spi_console)?,
        "iso9797m2" => CryptotestAesPadding::Iso9797M2.send(spi_console)?,
        _ => panic!("Invalid AES padding scheme"),
    };

    let mut iv: ArrayVec<u8, AES_BLOCK_BYTES>;
    match &test_case.iv {
        Some(iv_val) => {
            iv = ArrayVec::new();
            iv.try_extend_from_slice(iv_val)?
        }
        None => iv = ArrayVec::from([0; AES_BLOCK_BYTES]),
    }

    let mut key: ArrayVec<u8, AES_CMD_MAX_KEY_BYTES> = ArrayVec::new();
    key.try_extend_from_slice(&test_case.key)?;

    // Configure input and output based on operation
    let input_len;
    let mut input: ArrayVec<u8, AES_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    let expected_output;
    match test_case.operation.as_str() {
        "encrypt" => {
            input.try_extend_from_slice(&test_case.plaintext)?;
            input_len = test_case.plaintext.len();
            expected_output = &test_case.ciphertext;
        }
        "decrypt" => {
            input.try_extend_from_slice(&test_case.ciphertext)?;
            input_len = test_case.ciphertext.len();
            expected_output = &test_case.plaintext;
        }
        _ => panic!("Invalid AES operation"),
    }

    CryptotestAesData {
        key,
        key_length: test_case.key_len / 8,
        iv,
        input,
        input_len,
    }
    .send(spi_console)?;

    let aes_output = CryptotestAesOutput::recv(spi_console, opts.timeout, false, false)?;
    assert_eq!(
        aes_output.output[0..input_len],
        expected_output[0..input_len]
    );
    Ok(())
}

fn test_aes(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let test_vector_files = &opts.aes_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let aes_tests: Vec<AesTestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run
        let stride = min(skip_stride, aes_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for aes_test in &aes_tests {
            test_counter += 1;

            if (test_counter as usize % stride) != offset {
                // Skip test
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_aes_testcase(aes_test, opts, &spi_console_device)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_aes, &opts, &transport);
    Ok(())
}
