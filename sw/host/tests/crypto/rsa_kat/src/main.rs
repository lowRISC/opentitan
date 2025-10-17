// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use clap::Parser;
use std::fs;
use std::time::Duration;

use serde::Deserialize;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::rsa_commands::{
    CryptotestRsaVerify, CryptotestRsaVerifyResp, RsaSubcommand,
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

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    rsa_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct RsaTestCase {
    algorithm: String,
    padding: String,
    security_level: usize,
    hash_alg: String,
    message: Vec<u8>,
    n: Vec<u8>,
    e: u32,
    signature: Vec<u8>,
    result: bool,
}

fn run_rsa_testcase(
    test_case: &RsaTestCase,
    opts: &Opts,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    assert_eq!(test_case.algorithm.as_str(), "rsa");
    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaVerify.send(spi_console)?;

    // Configure hashing.
    let hashing = match test_case.hash_alg.as_str() {
        "sha-256" => 0,
        "sha-384" => 1,
        "sha-512" => 2,
        "sha3-256" => 3,
        "sha3-384" => 4,
        "sha3-512" => 5,
        "shake-128" => 6,
        "shake-256" => 7,
        _ => panic!("Invalid hashing mode"),
    };

    // Configure padding mode.
    let padding = match test_case.padding.as_str() {
        "pkcs1_1.5" => 0,
        "pss" => 1,
        _ => panic!("Invalid padding mode"),
    };

    // Convert the inputs into the expected format for the CL.
    let n: Vec<_> = test_case.n.iter().copied().rev().collect();
    let signature: Vec<_> = test_case.signature.iter().copied().rev().collect();

    CryptotestRsaVerify {
        msg: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
        msg_len: test_case.message.len(),
        e: test_case.e,
        n: ArrayVec::try_from(n.as_slice()).unwrap(),
        security_level: test_case.security_level,
        sig: ArrayVec::try_from(signature.as_slice()).unwrap(),
        sig_len: test_case.signature.len(),
        hashing,
        padding,
    }
    .send(spi_console)?;

    let rsa_verify_resp = CryptotestRsaVerifyResp::recv(spi_console, opts.timeout, false)?;
    assert_eq!(rsa_verify_resp.result, test_case.result);

    Ok(())
}

fn test_rsa(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let test_vector_files = &opts.rsa_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let rsa_tests: Vec<RsaTestCase> = serde_json::from_str(&raw_json)?;

        for rsa_test in &rsa_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_rsa_testcase(rsa_test, opts, &spi_console_device)?;
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;
    execute_test!(test_rsa, &opts, &transport);
    Ok(())
}
