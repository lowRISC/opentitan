// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::str::FromStr;
use std::time::Duration;

use anyhow::{Context, Result};
use clap::Parser;
use serde::Deserialize;

use pentest_commands::commands::PenetrationtestCommand;
use pentest_commands::fi_otp_commands::OtpFiSubcommand;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;
use pentest_lib::filter_response_common;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    #[arg(long, num_args = 1..)]
    fi_otp_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct FiOtpTestCase {
    test_case_id: usize,
    command: String,
    // Input only needed for the "Init" subcommand.
    #[serde(default)]
    input: String,
    expected_output: Vec<String>,
}

fn filter_response(response: serde_json::Value) -> serde_json::Map<String, serde_json::Value> {
    // Filter common items.
    let response_common_filtered = filter_response_common(response.clone());
    // Filter test-specifc items.
    let mut map: serde_json::Map<String, serde_json::Value> = response_common_filtered.clone();
    // Remove these entries as the test just returns the OTP content, which could
    // be different for different configurations.
    map.remove("hw_cfg_comp");
    map.remove("hw_cfg_fi");
    map.remove("owner_sw_cfg_comp");
    map.remove("owner_sw_cfg_fi");
    map.remove("vendor_test_comp");
    map.remove("vendor_test_fi");

    map
}

fn run_fi_otp_testcase(
    test_case: &FiOtpTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "test case: {}, test: {}",
        test_case.test_case_id,
        test_case.command
    );
    PenetrationtestCommand::OtpFi.send(uart)?;

    // Send test subcommand.
    OtpFiSubcommand::from_str(test_case.command.as_str())
        .context("unsupported Otp FI subcommand")?
        .send(uart)?;

    // Check if we need to send an input.
    if !test_case.input.is_empty() {
        let input: serde_json::Value = serde_json::from_str(test_case.input.as_str()).unwrap();
        input.send(uart)?;
    }

    // Check test outputs
    if !test_case.expected_output.is_empty() {
        for exp_output in test_case.expected_output.iter() {
            // Get test output & filter.
            let output = serde_json::Value::recv(
                uart,
                opts.timeout,
                /*quiet=*/ false,
                /*skip_crc=*/ false,
            )?;
            // Only check non empty JSON responses.
            if output.as_object().is_some() {
                let output_received = filter_response(output.clone());

                // Filter expected output.
                let exp_output: serde_json::Value =
                    serde_json::from_str(exp_output.as_str()).unwrap();
                let output_expected = filter_response(exp_output.clone());

                // Check received with expected output.
                if output_expected != output_received {
                    log::info!(
                        "FAILED {} test #{}: expected = '{}', actual = '{}'",
                        test_case.command,
                        test_case.test_case_id,
                        exp_output,
                        output
                    );
                    *fail_counter += 1;
                }
            }
        }
    }

    Ok(())
}

fn test_fi_otp(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.fi_otp_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let fi_otp_tests: Vec<FiOtpTestCase> = serde_json::from_str(&raw_json)?;
        for fi_otp_test in &fi_otp_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_fi_otp_testcase(fi_otp_test, opts, &*uart, &mut fail_counter)?;
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
    execute_test!(test_fi_otp, &opts, &transport);
    Ok(())
}
