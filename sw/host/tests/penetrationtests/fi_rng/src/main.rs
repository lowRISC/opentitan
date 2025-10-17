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
use pentest_commands::fi_rng_commands::RngFiSubcommand;

use opentitanlib::app::{TransportWrapper, UartRx};
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
    fi_rng_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct FiRngTestCase {
    test_case_id: usize,
    command: String,
    // Input only needed for the "Init" subcommand.
    #[serde(default)]
    input: String,
    #[serde(default)]
    sensors: String,
    #[serde(default)]
    alerts: String,
    #[serde(default)]
    expected_output: Vec<String>,
    #[serde(default)]
    flaky_expected_output: Vec<String>,
    #[serde(default)]
    reset: bool,
}

fn filter_response(response: serde_json::Value) -> serde_json::Map<String, serde_json::Value> {
    // Filter common items.
    let response_common_filtered = filter_response_common(response.clone());
    // Filter test-specifc items.
    let mut map: serde_json::Map<String, serde_json::Value> = response_common_filtered.clone();
    // RAND is random data.
    map.remove("rand");

    map
}

fn run_fi_rng_testcase(
    test_case: &FiRngTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "test case: {}, test: {}",
        test_case.test_case_id,
        test_case.command
    );
    PenetrationtestCommand::RngFi.send(uart)?;

    // Send test subcommand.
    RngFiSubcommand::from_str(test_case.command.as_str())
        .context("unsupported RNG FI subcommand")?
        .send(uart)?;

    // Check if we need to send an input.
    if !test_case.input.is_empty() {
        let input: serde_json::Value = serde_json::from_str(test_case.input.as_str()).unwrap();
        input.send(uart)?;
    }

    // Check if we need to send sensor info.
    if !test_case.sensors.is_empty() {
        let sensors: serde_json::Value = serde_json::from_str(test_case.sensors.as_str()).unwrap();
        sensors.send(uart)?;
    }

    // Check if we need to send alert info.
    if !test_case.alerts.is_empty() {
        let alerts: serde_json::Value = serde_json::from_str(test_case.alerts.as_str()).unwrap();
        alerts.send(uart)?;
    }

    // Check test outputs
    if !test_case.expected_output.is_empty() {
        for exp_output in test_case.expected_output.iter() {
            // Get test output & filter.
            let output = serde_json::Value::recv(uart, opts.timeout, false)?;
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
                        "FAILED {} test #{}: expected = '{}', actual = '{}'\n",
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

    // Check flaky test outputs
    if !test_case.flaky_expected_output.is_empty() {
        for exp_output in test_case.flaky_expected_output.iter() {
            // Get test output & filter.
            let output = serde_json::Value::recv(uart, opts.timeout, false)?;
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
                        "Flaky result of {} test #{}: expected = '{}', actual = '{}'\n",
                        test_case.command,
                        test_case.test_case_id,
                        exp_output,
                        output
                    );
                }
                // Do not let the flaky test influence the fail counter.
            }
        }
    }

    Ok(())
}

fn test_fi_rng(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running ", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.fi_rng_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let fi_rng_tests: Vec<FiRngTestCase> = serde_json::from_str(&raw_json)?;
        for fi_rng_test in &fi_rng_tests {
            if fi_rng_test.reset {
                transport.reset_with_delay(UartRx::Clear, Duration::from_millis(750))?;
            } else {
                test_counter += 1;
                log::info!("Test counter: {}", test_counter);
                run_fi_rng_testcase(fi_rng_test, opts, &*uart, &mut fail_counter)?;
            }
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
    execute_test!(test_fi_rng, &opts, &transport);
    Ok(())
}
