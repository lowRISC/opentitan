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
use pentest_commands::sca_otbn_commands::OtbnScaSubcommand;

use opentitanlib::app::TransportWrapper;
use opentitanlib::execute_test;
use opentitanlib::io::uart::Uart;
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
    sca_otbn_json: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct ScaOtbnTestCase {
    test_case_id: usize,
    command: String,
    #[serde(default)]
    input: String,
    #[serde(default)]
    iterations: String,
    #[serde(default)]
    masking: String,
    #[serde(default)]
    expected_output: String,
}

fn filter_response(response: serde_json::Value) -> serde_json::Map<String, serde_json::Value> {
    let mut map: serde_json::Map<String, serde_json::Value> = response.as_object().unwrap().clone();
    // Device ID is different for each device.
    map.remove("device_id");

    map
}

fn run_sca_otbn_testcase(
    test_case: &ScaOtbnTestCase,
    opts: &Opts,
    uart: &dyn Uart,
    fail_counter: &mut u32,
) -> Result<()> {
    log::info!(
        "test case: {}, test: {}",
        test_case.test_case_id,
        test_case.command
    );
    PenetrationtestCommand::OtbnSca.send(uart)?;

    // Send test subcommand.
    OtbnScaSubcommand::from_str(test_case.command.as_str())
        .context("unsupported OTBN SCA subcommand")?
        .send(uart)?;

    // Check if we need to send an input.
    if !test_case.iterations.is_empty() {
        let iterations: serde_json::Value =
            serde_json::from_str(test_case.iterations.as_str()).unwrap();
        iterations.send(uart)?;
    }

    if !test_case.masking.is_empty() {
        let masking: serde_json::Value = serde_json::from_str(test_case.masking.as_str()).unwrap();
        masking.send(uart)?;
    }

    if !test_case.input.is_empty() {
        let input: serde_json::Value = serde_json::from_str(test_case.input.as_str()).unwrap();
        input.send(uart)?;
    }

    if !test_case.expected_output.is_empty() {
        // Get test output & filter.
        let output = serde_json::Value::recv(
            uart,
            opts.timeout,
            /*quiet=*/ false,
            /*skip_crc=*/ false,
        )?;
        let output_received = filter_response(output.clone());

        // Filter expected output.
        let exp_output: serde_json::Value =
            serde_json::from_str(test_case.expected_output.as_str()).unwrap();
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

    Ok(())
}

fn test_sca_otbn(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Running [^\r\n]*", opts.timeout)?;

    let mut test_counter = 0u32;
    let mut fail_counter = 0u32;
    let test_vector_files = &opts.sca_otbn_json;
    for file in test_vector_files {
        let raw_json = fs::read_to_string(file)?;
        let sca_otbn_tests: Vec<ScaOtbnTestCase> = serde_json::from_str(&raw_json)?;
        for sca_otbn_test in &sca_otbn_tests {
            test_counter += 1;
            log::info!("Test counter: {}", test_counter);
            run_sca_otbn_testcase(sca_otbn_test, opts, &*uart, &mut fail_counter)?;
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
    execute_test!(test_sca_otbn, &opts, &transport);
    Ok(())
}
