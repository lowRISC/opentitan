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
use cryptotest_commands::hkdf_commands::{
    CryptotestHkdfData, CryptotestHkdfHashAlg, CryptotestHkdfOkm,
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
    #[arg(long, value_parser = humantime::parse_duration, default_value = "30s")]
    timeout: Duration,

    // Reduce number of tests that are run by this factor.
    #[arg(long, default_value_t = 0usize)]
    skip_stride: usize,

    // Seed value for random number generator.
    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, num_args = 1..)]
    hkdf_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct HkdfTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    hash_alg: String,
    ikm: Vec<u8>,
    salt: Vec<u8>,
    info: Vec<u8>,
    size: usize,
    okm: Vec<u8>,
    result: bool,
}

const HKDF_CMD_MAX_IKM_BYTES: usize = 128;
const HKDF_CMD_MAX_SALT_BYTES: usize = 128;
const HKDF_CMD_MAX_INFO_BYTES: usize = 128;

fn run_hkdf_testcase(
    test_case: &HkdfTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );
    assert_eq!(test_case.algorithm.as_str(), "hkdf");
    CryptotestCommand::Hkdf.send(spi_console)?;

    assert!(
        test_case.ikm.len() <= HKDF_CMD_MAX_IKM_BYTES,
        "IKM too long for device firmware configuration (got = {}, max = {})",
        test_case.ikm.len(),
        HKDF_CMD_MAX_IKM_BYTES,
    );
    assert!(
        test_case.salt.len() <= HKDF_CMD_MAX_SALT_BYTES,
        "Salt too long for device firmware configuration (got = {}, max = {})",
        test_case.salt.len(),
        HKDF_CMD_MAX_SALT_BYTES,
    );
    assert!(
        test_case.info.len() <= HKDF_CMD_MAX_INFO_BYTES,
        "Info too long for device firmware configuration (got = {}, max = {})",
        test_case.info.len(),
        HKDF_CMD_MAX_INFO_BYTES,
    );

    match test_case.hash_alg.as_str() {
        "sha-256" => CryptotestHkdfHashAlg::Sha256,
        "sha-384" => CryptotestHkdfHashAlg::Sha384,
        "sha-512" => CryptotestHkdfHashAlg::Sha512,
        _ => panic!("Unsupported HKDF hash mode"),
    }
    .send(spi_console)?;

    CryptotestHkdfData {
        ikm: ArrayVec::try_from(test_case.ikm.as_slice()).unwrap(),
        ikm_len: test_case.ikm.len(),
        salt: ArrayVec::try_from(test_case.salt.as_slice()).unwrap(),
        salt_len: test_case.salt.len(),
        info: ArrayVec::try_from(test_case.info.as_slice()).unwrap(),
        info_len: test_case.info.len(),
        okm_len: test_case.size,
    }
    .send(spi_console)?;

    let hkdf_okm = CryptotestHkdfOkm::recv(spi_console, opts.timeout, false, false)?;
    let success = if !hkdf_okm.status_ok || test_case.okm.len() != hkdf_okm.okm_len {
        false
    } else {
        test_case.okm[..] == hkdf_okm.okm[..test_case.okm.len()]
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

fn test_hkdf(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let test_vector_files = &opts.hkdf_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let hkdf_tests: Vec<HkdfTestCase> = serde_json::from_str(&raw_json)?;

        let stride = min(skip_stride, hkdf_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for hkdf_test in &hkdf_tests {
            test_counter += 1;

            if (hkdf_test.test_case_id % stride) != offset {
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_hkdf_testcase(hkdf_test, opts, &spi_console_device, &mut fail_counter)?;
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
    execute_test!(test_hkdf, &opts, &transport);
    Ok(())
}
