// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::rpc::ConsoleSend;
use opentitanlib::uart::console::UartConsole;

mod cshake;
mod hmac;
mod rsa;

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

    // Input ACVP JSON test vector file.
    #[arg(long)]
    input: Option<std::path::PathBuf>,

    // Output ACVP JSON result file.
    #[arg(long)]
    output: Option<std::path::PathBuf>,

    // ACVP JSON result file containing expected outputs.
    #[arg(long)]
    expected: Option<std::path::PathBuf>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all_fields = "camelCase")]
#[serde(untagged)]
enum AcvpVectors {
    Header {
        url: String,
        vector_set_urls: Vec<String>,
        time: String,
    },
    Hmac(hmac::HmacTestVectorSet),
    Cshake(cshake::CshakeTestVectorSet),
    Rsa(rsa::RsaTestVectorSet),
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all_fields = "camelCase")]
#[serde(untagged)]
enum AcvpResults {
    Header {
        url: String,
        vector_set_urls: Vec<String>,
        time: String,
    },
    Hmac(hmac::HmacResultVectorSet),
    Cshake(cshake::CshakeResultVectorSet),
    Rsa(rsa::RsaResultVectorSet),
}

fn validate_subset(actual: &[AcvpResults], expected_json: &serde_json::Value) -> Result<()> {
    let exp_array = expected_json
        .as_array()
        .ok_or_else(|| std::io::Error::other("Expected JSON is not an array"))?;

    if actual.len() != exp_array.len() {
        return Err(std::io::Error::other(
            "ACVP structure mismatch: different number of vector sets",
        )
        .into());
    }

    let act_json = serde_json::to_value(actual)?;
    let act_array = act_json.as_array().unwrap();

    for (a_idx, (act_val, exp_val)) in act_array.iter().zip(exp_array.iter()).enumerate() {
        if act_val.get("url").is_some() {
            continue;
        }

        let act_tgs = act_val.get("testGroups").and_then(|t| t.as_array());
        let exp_tgs = exp_val.get("testGroups").and_then(|t| t.as_array());

        if let (Some(act_tgs), Some(exp_tgs)) = (act_tgs, exp_tgs) {
            for act_tg in act_tgs {
                let tg_id = act_tg.get("tgId").unwrap();
                let exp_tg = exp_tgs
                    .iter()
                    .find(|tg| tg.get("tgId") == Some(tg_id))
                    .ok_or_else(|| {
                        std::io::Error::other(format!(
                            "Test Group {} missing in expected JSON",
                            tg_id
                        ))
                    })?;

                let act_tests = act_tg.get("tests").unwrap().as_array().unwrap();
                let exp_tests = exp_tg.get("tests").unwrap().as_array().unwrap();

                for act_tc in act_tests {
                    let tc_id = act_tc.get("tcId").unwrap();
                    let exp_tc = exp_tests
                        .iter()
                        .find(|tc| tc.get("tcId") == Some(tc_id))
                        .ok_or_else(|| {
                            std::io::Error::other(format!(
                                "Test Case {} missing in expected JSON",
                                tc_id
                            ))
                        })?;
                    if act_tc != exp_tc {
                        return Err(
                            std::io::Error::other(format!("Test Case {} mismatch", tc_id)).into(),
                        );
                    }
                }
            }
        } else {
            return Err(std::io::Error::other(format!(
                "ACVP structure mismatch at index {}",
                a_idx
            ))
            .into());
        }
    }
    Ok(())
}

fn run<R: std::io::Read, W: std::io::Write>(
    opts: &Opts,
    transport: &TransportWrapper,
    input: R,
    expected: Option<R>,
    output: Option<W>,
) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(
        &*spi,
        None,
        /*ignore_frame_num=*/ false,
        Some(opts.init.backend_opts.interface.as_str()),
    )?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running [^\r\n]*", opts.timeout)?;

    let acvp_vectors: Vec<AcvpVectors> = serde_json::from_reader(input)?;
    let mut acvp_results: Vec<AcvpResults> = Vec::with_capacity(acvp_vectors.len());

    for v in acvp_vectors {
        match v {
            AcvpVectors::Header {
                url,
                vector_set_urls,
                time,
            } => acvp_results.push(AcvpResults::Header {
                url,
                vector_set_urls,
                time,
            }),
            AcvpVectors::Hmac(vs) => {
                acvp_results.push(AcvpResults::Hmac(hmac::run_hmac_vector_set(
                    opts.timeout,
                    &spi_console_device,
                    &vs,
                    opts.skip_stride,
                    opts.seed,
                )?))
            }
            AcvpVectors::Cshake(vs) => {
                acvp_results.push(AcvpResults::Cshake(cshake::run_cshake_vector_set(
                    opts.timeout,
                    &spi_console_device,
                    &vs,
                    opts.skip_stride,
                    opts.seed,
                )?))
            }
            AcvpVectors::Rsa(vs) => acvp_results.push(AcvpResults::Rsa(rsa::run_rsa_vector_set(
                opts.timeout,
                &spi_console_device,
                &vs,
                opts.skip_stride,
                opts.seed,
            )?)),
        }
    }
    if let Some(w) = output {
        serde_json::to_writer_pretty(w, &acvp_results)?;
    }
    if let Some(r) = expected {
        let expected_results_json: serde_json::Value = serde_json::from_reader(r)?;
        validate_subset(&acvp_results, &expected_results_json)?;
        if opts.skip_stride == 0 {
            let acvp_results_json = serde_json::to_value(&acvp_results)?;
            if acvp_results_json != expected_results_json {
                return Err(std::io::Error::other(
                    "ACVP result mismatch (strict parity check failed)",
                )
                .into());
            }
        }
    }
    CryptotestCommand::Quit.send(&spi_console_device)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"PASS!|FAIL!", opts.timeout * 10)?;
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();

    let transport = opts.init.init_target()?;

    // Note: Missing input, expected and output arguments are intentionally
    // non-fatal to support running this test harness without arguments in test
    // scripts. This ensures that the harness and firmware will successfully
    // build and that the harness will bootstrap the target before discovering
    // the "missing" arguments.
    let Some(ref input_path) = opts.input else {
        log::warn!("Missing input ACVP JSON file");
        return Ok(());
    };
    if opts.expected.is_none() && opts.output.is_none() {
        log::warn!("Missing expected/output ACVP JSON files");
        return Ok(());
    }

    let f = std::fs::File::open(input_path).inspect_err(|e| log::error!("open input file: {e}"))?;
    let input = std::io::BufReader::new(f);

    let expected = match &opts.expected {
        Some(expected_path) => {
            let f = std::fs::File::open(expected_path)
                .inspect_err(|e| log::error!("open expected file: {e}"))?;
            Some(std::io::BufReader::new(f))
        }
        None => None,
    };
    let output = match &opts.output {
        Some(output_path) => {
            let f = std::fs::File::create(output_path)
                .inspect_err(|e| log::error!("open output file: {e}"))?;
            Some(std::io::BufWriter::new(f))
        }
        None => None,
    };

    run(&opts, &transport, input, expected, output)
}
