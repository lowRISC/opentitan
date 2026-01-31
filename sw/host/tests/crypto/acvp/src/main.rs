// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

mod hmac;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    // Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

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
}

fn run<R: std::io::Read, W: std::io::Write>(
    opts: &Opts,
    transport: &TransportWrapper,
    input: R,
    expected: Option<R>,
    output: Option<W>,
) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None, /*ignore_frame_num=*/ false)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running ", opts.timeout)?;

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
            AcvpVectors::Hmac(vs) => acvp_results.push(AcvpResults::Hmac(
                hmac::run_hmac_vector_set(opts.timeout, &spi_console_device, &vs)?,
            )),
        }
    }
    if let Some(w) = output {
        serde_json::to_writer_pretty(w, &acvp_results)?;
    }
    if let Some(r) = expected {
        let expected_results: Vec<AcvpResults> = serde_json::from_reader(r)?;
        if acvp_results != expected_results {
            return Err(std::io::Error::other("ACVP result mismatch").into());
        }
    }
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
