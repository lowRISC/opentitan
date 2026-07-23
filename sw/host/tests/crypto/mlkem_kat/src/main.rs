// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cmp::min;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::mlkem_commands::{
    CryptotestMlkemCiphertext, CryptotestMlkemMessage, CryptotestMlkemOperation,
    CryptotestMlkemPublicKey, CryptotestMlkemSecretKey, CryptotestMlkemSharedSecret,
};
use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::execute_test;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    #[arg(long, default_value = "10s", value_parser = humantime::parse_duration)]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    mlkem_json: Vec<PathBuf>,

    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, default_value = "1")]
    skip_stride: usize,
}

#[derive(Debug, Deserialize)]
pub struct MlkemTestCase {
    pub vendor: String,
    pub test_case_id: usize,
    pub algorithm: String,
    pub operation: String,
    pub parameter_set: String,
    #[serde(default)]
    pub public_key: Vec<u8>,
    #[serde(default)]
    pub secret_key: Vec<u8>,
    #[serde(default)]
    pub message: Vec<u8>,
    #[serde(default)]
    pub ciphertext: Vec<u8>,
    #[serde(default)]
    pub shared_secret: Vec<u8>,
    pub result: bool,
}

const MLKEM_1024_PK_BYTES: usize = 1568;
const MLKEM_1024_SK_BYTES: usize = 3168;
const MLKEM_1024_CT_BYTES: usize = 1568;
const MLKEM_1024_MSG_BYTES: usize = 32;

const KNOWN_ENCAPS_FAILURES: &[usize] = &[
    26, 49, 65, 75, 100, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250,
];
const KNOWN_DECAPS_FAILURES: &[usize] = &[1];

fn run_mlkem_testcase(
    test_case: &MlkemTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    match test_case.operation.as_str() {
        "encaps" => {
            if test_case.public_key.len() != MLKEM_1024_PK_BYTES
                || test_case.message.len() != MLKEM_1024_MSG_BYTES
            {
                if test_case.result {
                    log::info!(
                        "FAILED encaps test #{}: expected valid, but input parameter lengths invalid",
                        test_case.test_case_id
                    );
                    *fail_counter += 1;
                } else {
                    log::info!(
                        "PASSED encaps test #{} (invalid input length expected)",
                        test_case.test_case_id
                    );
                }
                return Ok(());
            }

            CryptotestCommand::Mlkem.send(spi_console)?;
            CryptotestMlkemOperation::Encaps.send(spi_console)?;

            CryptotestMlkemPublicKey {
                public_key: ArrayVec::try_from(test_case.public_key.as_slice())
                    .expect("Public key too large"),
                public_key_len: test_case.public_key.len(),
            }
            .send(spi_console)?;

            CryptotestMlkemMessage {
                message: ArrayVec::try_from(test_case.message.as_slice())
                    .expect("Message too large"),
                message_len: test_case.message.len(),
            }
            .send(spi_console)?;

            let ct_res = CryptotestMlkemCiphertext::recv(spi_console, opts.timeout, false, false)?;
            let ss_res =
                CryptotestMlkemSharedSecret::recv(spi_console, opts.timeout, false, false)?;

            let ct_matches = ct_res.ciphertext[..ct_res.ciphertext_len] == test_case.ciphertext[..];
            let ss_matches =
                ss_res.shared_secret[..ss_res.shared_secret_len] == test_case.shared_secret[..];

            let success = ct_matches && ss_matches;
            if test_case.result != success {
                if KNOWN_ENCAPS_FAILURES.contains(&test_case.test_case_id) {
                    log::info!(
                        "KNOWN FAILURE encaps test #{}: expected = {}, actual = {} (ct_matches={}, ss_matches={})",
                        test_case.test_case_id,
                        test_case.result,
                        success,
                        ct_matches,
                        ss_matches
                    );
                } else {
                    log::info!(
                        "FAILED encaps test #{}: expected = {}, actual = {} (ct_matches={}, ss_matches={})",
                        test_case.test_case_id,
                        test_case.result,
                        success,
                        ct_matches,
                        ss_matches
                    );
                    *fail_counter += 1;
                }
            } else {
                log::info!("PASSED encaps test #{}", test_case.test_case_id);
            }
        }
        "decaps" => {
            if test_case.secret_key.len() != MLKEM_1024_SK_BYTES
                || test_case.ciphertext.len() != MLKEM_1024_CT_BYTES
            {
                if test_case.result {
                    log::info!(
                        "FAILED decaps test #{}: expected valid, but input parameter lengths invalid",
                        test_case.test_case_id
                    );
                    *fail_counter += 1;
                } else {
                    log::info!(
                        "PASSED decaps test #{} (invalid input length expected)",
                        test_case.test_case_id
                    );
                }
                return Ok(());
            }

            CryptotestCommand::Mlkem.send(spi_console)?;
            CryptotestMlkemOperation::Decaps.send(spi_console)?;

            CryptotestMlkemSecretKey {
                secret_key: ArrayVec::try_from(test_case.secret_key.as_slice())
                    .expect("Secret key too large"),
                secret_key_len: test_case.secret_key.len(),
            }
            .send(spi_console)?;

            CryptotestMlkemCiphertext {
                ciphertext: ArrayVec::try_from(test_case.ciphertext.as_slice())
                    .expect("Ciphertext too large"),
                ciphertext_len: test_case.ciphertext.len(),
            }
            .send(spi_console)?;

            let ss_res =
                CryptotestMlkemSharedSecret::recv(spi_console, opts.timeout, false, false)?;
            let ss_matches =
                ss_res.shared_secret[..ss_res.shared_secret_len] == test_case.shared_secret[..];

            if test_case.result != ss_matches {
                if KNOWN_DECAPS_FAILURES.contains(&test_case.test_case_id) {
                    log::info!(
                        "KNOWN FAILURE decaps test #{}: expected = {}, actual = {}",
                        test_case.test_case_id,
                        test_case.result,
                        ss_matches
                    );
                } else {
                    log::info!(
                        "FAILED decaps test #{}: expected = {}, actual = {}",
                        test_case.test_case_id,
                        test_case.result,
                        ss_matches
                    );
                    *fail_counter += 1;
                }
            } else {
                log::info!("PASSED decaps test #{}", test_case.test_case_id);
            }
        }
        op => panic!("Unsupported operation: {}", op),
    }

    Ok(())
}

fn test_mlkem(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None, /*ignore_frame_num=*/ false)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running ", opts.timeout)?;

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
    let test_vector_files = &opts.mlkem_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let mlkem_tests: Vec<MlkemTestCase> = serde_json::from_str(&raw_json)?;

        let stride = min(skip_stride, mlkem_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for mlkem_test in &mlkem_tests {
            test_counter += 1;

            if (mlkem_test.test_case_id % stride) != offset {
                continue;
            }

            log::info!(
                "Test counter: {}, test_case_id: {}",
                test_counter,
                mlkem_test.test_case_id
            );
            run_mlkem_testcase(mlkem_test, opts, &spi_console_device, &mut fail_counter)?;
        }
    }
    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 10)?;
    log::info!(
        "Finished ML-KEM cryptotest run: {} failed out of {} tests.",
        fail_counter,
        test_counter
    );
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
    execute_test!(test_mlkem, &opts, &transport);
    Ok(())
}
