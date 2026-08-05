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
use cryptotest_commands::mldsa_commands::{
    CryptotestMldsaContext, CryptotestMldsaMessage, CryptotestMldsaOperation,
    CryptotestMldsaPrivateKeySeed, CryptotestMldsaPublicKey, CryptotestMldsaSignature,
    CryptotestMldsaVerifyResult,
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

    #[arg(long, default_value = "30s", value_parser = humantime::parse_duration)]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    mldsa_json: Vec<PathBuf>,

    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, default_value = "1")]
    skip_stride: usize,
}

#[derive(Debug, Deserialize)]
pub struct MldsaTestCase {
    pub vendor: String,
    pub test_case_id: usize,
    pub algorithm: String,
    pub operation: String,
    pub parameter_set: String,
    #[serde(default)]
    pub private_seed: Vec<u8>,
    #[serde(default)]
    pub public_key: Vec<u8>,
    #[serde(default)]
    pub message: Vec<u8>,
    #[serde(default)]
    pub context: Vec<u8>,
    #[serde(default)]
    pub rnd: Vec<u8>,
    #[serde(default)]
    pub signature: Vec<u8>,
    pub result: bool,
}

const KNOWN_SIGN_FAILURES: &[usize] = &[];
const KNOWN_VERIFY_FAILURES: &[usize] = &[];

fn run_mldsa_testcase(
    test_case: &MldsaTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    match test_case.operation.as_str() {
        "sign" => {
            if !test_case.rnd.is_empty() {
                log::info!(
                    "SKIPPED sign test #{} (external rnd not supported)",
                    test_case.test_case_id
                );
                return Ok(());
            }

            CryptotestCommand::Mldsa.send(spi_console)?;
            CryptotestMldsaOperation::Sign.send(spi_console)?;

            CryptotestMldsaPrivateKeySeed {
                private_seed: ArrayVec::try_from(test_case.private_seed.as_slice())
                    .expect("Private seed too large"),
                private_seed_len: test_case.private_seed.len(),
            }
            .send(spi_console)?;

            CryptotestMldsaMessage {
                message: ArrayVec::try_from(test_case.message.as_slice())
                    .expect("Message too large"),
                message_len: test_case.message.len(),
            }
            .send(spi_console)?;

            CryptotestMldsaContext {
                context: ArrayVec::try_from(test_case.context.as_slice())
                    .expect("Context too large"),
                context_len: test_case.context.len(),
            }
            .send(spi_console)?;

            let sig_res = CryptotestMldsaSignature::recv(spi_console, opts.timeout, false, false)?;
            let test_passed = if !test_case.result {
                sig_res.signature_len == 0
            } else {
                sig_res.signature[..sig_res.signature_len] == test_case.signature[..]
            };

            if !test_passed {
                if KNOWN_SIGN_FAILURES.contains(&test_case.test_case_id) {
                    log::info!(
                        "KNOWN FAILURE sign test #{}: expected result = {}",
                        test_case.test_case_id,
                        test_case.result
                    );
                } else {
                    log::info!(
                        "FAILED sign test #{}: expected result = {}",
                        test_case.test_case_id,
                        test_case.result
                    );
                    *fail_counter += 1;
                }
            } else {
                log::info!("PASSED sign test #{}", test_case.test_case_id);
            }
        }
        "verify" => {
            CryptotestCommand::Mldsa.send(spi_console)?;
            CryptotestMldsaOperation::Verify.send(spi_console)?;

            CryptotestMldsaPublicKey {
                public_key: ArrayVec::try_from(test_case.public_key.as_slice())
                    .expect("Public key too large"),
                public_key_len: test_case.public_key.len(),
            }
            .send(spi_console)?;

            CryptotestMldsaMessage {
                message: ArrayVec::try_from(test_case.message.as_slice())
                    .expect("Message too large"),
                message_len: test_case.message.len(),
            }
            .send(spi_console)?;

            CryptotestMldsaContext {
                context: ArrayVec::try_from(test_case.context.as_slice())
                    .expect("Context too large"),
                context_len: test_case.context.len(),
            }
            .send(spi_console)?;

            CryptotestMldsaSignature {
                signature: ArrayVec::try_from(test_case.signature.as_slice())
                    .expect("Signature too large"),
                signature_len: test_case.signature.len(),
            }
            .send(spi_console)?;

            let res = CryptotestMldsaVerifyResult::recv(spi_console, opts.timeout, false, false)?;
            let success = res.valid;

            if test_case.result != success {
                if KNOWN_VERIFY_FAILURES.contains(&test_case.test_case_id) {
                    log::info!(
                        "KNOWN FAILURE verify test #{}: expected = {}, actual = {}",
                        test_case.test_case_id,
                        test_case.result,
                        success
                    );
                } else {
                    log::info!(
                        "FAILED verify test #{}: expected = {}, actual = {}",
                        test_case.test_case_id,
                        test_case.result,
                        success
                    );
                    *fail_counter += 1;
                }
            } else {
                log::info!("PASSED verify test #{}", test_case.test_case_id);
            }
        }
        op => panic!("Unsupported operation: {}", op),
    }

    Ok(())
}

fn test_mldsa(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let test_vector_files = &opts.mldsa_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let mldsa_tests: Vec<MldsaTestCase> = serde_json::from_str(&raw_json)?;

        let stride = min(skip_stride, mldsa_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for mldsa_test in &mldsa_tests {
            test_counter += 1;

            if (mldsa_test.test_case_id % stride) != offset {
                continue;
            }

            log::info!(
                "Test counter: {}, test_case_id: {}",
                test_counter,
                mldsa_test.test_case_id
            );
            run_mldsa_testcase(mldsa_test, opts, &spi_console_device, &mut fail_counter)?;
        }
    }
    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 20)?;
    log::info!(
        "Finished ML-DSA cryptotest run: {} failed out of {} tests.",
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
    execute_test!(test_mldsa, &opts, &transport);
    Ok(())
}
