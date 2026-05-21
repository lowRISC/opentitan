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
use cryptotest_commands::x25519_commands::{
    CryptotestX25519DeriveOutput, CryptotestX25519PrivateKey, CryptotestX25519PublicKey,
    X25519Subcommand,
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
    // If skip_stride is set to 0, all tests are run.
    #[arg(long, default_value_t = 0usize)]
    skip_stride: usize,

    // Seed value for random number generator.
    #[arg(long)]
    seed: Option<u64>,

    #[arg(long, num_args = 1..)]
    x25519_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct X25519TestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    private_key: Vec<u8>,
    public_key: Vec<u8>,
    shared_secret: Vec<u8>,
}

// Fixed sizes defined by the X25519 algorithm (RFC 7748).
const X25519_PRIVATE_KEY_BYTES: usize = 32;
const X25519_PUBLIC_KEY_BYTES: usize = 32;
const X25519_SHARED_SECRET_BYTES: usize = 32;

fn run_x25519_testcase(
    test_case: &X25519TestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
    failures: &mut Vec<String>,
    test_counter: usize,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );
    assert_eq!(test_case.algorithm.as_str(), "x25519");
    assert_eq!(
        test_case.private_key.len(),
        X25519_PRIVATE_KEY_BYTES,
        "X25519 private key must be exactly {} bytes (got {})",
        X25519_PRIVATE_KEY_BYTES,
        test_case.private_key.len(),
    );
    assert_eq!(
        test_case.public_key.len(),
        X25519_PUBLIC_KEY_BYTES,
        "X25519 public key must be exactly {} bytes (got {})",
        X25519_PUBLIC_KEY_BYTES,
        test_case.public_key.len(),
    );
    // Send X25519 Shared Secret Generation command.
    CryptotestCommand::X25519.send(spi_console)?;
    X25519Subcommand::X25519SSG.send(spi_console)?;

    // X25519 keys and shared secrets are in RFC 7748 little-endian byte order;
    // the test vectors are already in this format so no reversal is needed.
    CryptotestX25519PrivateKey {
        private_key: ArrayVec::try_from(test_case.private_key.as_slice())
            .expect("X25519 private key had unexpected length."),
        private_key_len: test_case.private_key.len(),
    }
    .send(spi_console)?;

    CryptotestX25519PublicKey {
        public_key: ArrayVec::try_from(test_case.public_key.as_slice())
            .expect("X25519 public key had unexpected length."),
        public_key_len: test_case.public_key.len(),
    }
    .send(spi_console)?;

    let output = CryptotestX25519DeriveOutput::recv(spi_console, opts.timeout, false, false)?;

    if output.shared_secret_len > X25519_SHARED_SECRET_BYTES {
        panic!(
            "X25519 returned shared secret length {} exceeds maximum {}.",
            output.shared_secret_len, X25519_SHARED_SECRET_BYTES
        );
    }

    let device_secret = &output.shared_secret[..output.shared_secret_len];

    let success = output.result && device_secret == test_case.shared_secret.as_slice();

    if !success {
        log::info!(
            "FAILED test #{}: device result = {}, device secret = {:02x?}",
            test_case.test_case_id,
            output.result,
            device_secret,
        );
        failures.push(format!("x25519 #{}", test_counter));
    }
    Ok(())
}

fn test_x25519(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
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
    let test_vector_files = &opts.x25519_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let x25519_tests: Vec<X25519TestCase> = serde_json::from_str(&raw_json)?;

        // Ensure that at least one test per JSON file is run.
        let stride = min(skip_stride, x25519_tests.len());
        let offset = start_offset % stride;
        log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

        for (i, x25519_test) in x25519_tests.iter().enumerate() {
            test_counter += 1;

            if (i % stride) != offset {
                // Skip test.
                continue;
            }

            log::info!("Test counter: {}", test_counter);
            run_x25519_testcase(
                x25519_test,
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
    execute_test!(test_x25519, &opts, &transport);
    Ok(())
}
