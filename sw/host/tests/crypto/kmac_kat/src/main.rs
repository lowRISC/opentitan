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
use cryptotest_commands::kmac_commands::{
    CryptotestKmacCustomizationString, CryptotestKmacKey, CryptotestKmacMessage,
    CryptotestKmacMode, CryptotestKmacRequiredTagLength, CryptotestKmacTag,
};

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    kmac_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct KmacTestCase {
    vendor: String,
    test_case_id: usize,
    algorithm: String,
    mode: usize,
    key: Vec<u8>,
    message: Vec<u8>,
    customization_string: Vec<u8>,
    tag: Vec<u8>,
    result: bool,
}

const KMAC_CMD_MAX_MESSAGE_BYTES: usize = 256;

// These values are limitations of OpenTitan's KMAC HWIP
const KMAC_CMD_MAX_CUSTOMIZATION_STRING_BYTES: usize = 36;
const KMAC_CMD_MAX_KEY_BYTES: usize = 64;

fn run_kmac_testcase(
    test_case: &KmacTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "vendor: {}, test case: {}",
        test_case.vendor,
        test_case.test_case_id
    );

    assert_eq!(test_case.algorithm.as_str(), "kmac");
    CryptotestCommand::Kmac.send(uart)?;

    assert!(
        test_case.key.len() <= KMAC_CMD_MAX_KEY_BYTES,
        "Key too long for device (got = {}, max = {})",
        test_case.key.len(),
        KMAC_CMD_MAX_KEY_BYTES,
    );
    assert!(
        test_case.message.len() <= KMAC_CMD_MAX_MESSAGE_BYTES,
        "Message too long for device firmware configuration (got = {}, max = {})",
        test_case.message.len(),
        KMAC_CMD_MAX_MESSAGE_BYTES,
    );
    assert!(
        test_case.customization_string.len() <= KMAC_CMD_MAX_CUSTOMIZATION_STRING_BYTES,
        "Customization string too long for device (got = {}, max = {})",
        test_case.customization_string.len(),
        KMAC_CMD_MAX_CUSTOMIZATION_STRING_BYTES,
    );

    match test_case.mode {
        128 => CryptotestKmacMode::Kmac128,
        256 => CryptotestKmacMode::Kmac256,
        _ => panic!("Unsupported KMAC mode"),
    }
    .send(uart)?;

    CryptotestKmacRequiredTagLength {
        // Set this to the expected tag length, so we guarantee we perform a fair comparison with
        // the expected value.
        required_tag_length: test_case.tag.len(),
    }
    .send(uart)?;

    CryptotestKmacKey {
        key: ArrayVec::try_from(test_case.key.as_slice()).unwrap(),
        key_len: test_case.key.len(),
    }
    .send(uart)?;

    CryptotestKmacMessage {
        message: ArrayVec::try_from(test_case.message.as_slice()).unwrap(),
        message_len: test_case.message.len(),
    }
    .send(uart)?;

    CryptotestKmacCustomizationString {
        customization_string: ArrayVec::try_from(test_case.customization_string.as_slice())
            .unwrap(),
        customization_string_len: test_case.customization_string.len(),
    }
    .send(uart)?;

    let kmac_tag = CryptotestKmacTag::recv(uart, opts.timeout, false)?;
    // Cryptolib could have chosen to return more tag bytes than we asked for. If it did, we can
    // ignore the extra ones.
    let success = test_case.tag[..] == kmac_tag.tag[..test_case.tag.len()];
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

fn test_kmac(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.kmac_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let kmac_tests: Vec<KmacTestCase> = serde_json::from_str(&raw_json)?;

        for kmac_test in &kmac_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_kmac_testcase(kmac_test, opts, &*uart, &mut fail_counter)?;
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
    execute_test!(test_kmac, &opts, &transport);
    Ok(())
}
