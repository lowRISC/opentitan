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

mod aes;
mod cshake;
mod ecdsa;
mod eddsa;
mod hmac;
mod kmac;
mod rsa;
mod x25519;

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

    // Run sigGen test vectors from the input file.
    // sigGen results are non-deterministic and are never compared against --expected.
    #[arg(long, default_value_t = false)]
    run_siggen: bool,

    // Run keyGen test vectors from the input file.
    // keyGen results are non-deterministic and are never compared against --expected.
    #[arg(long, default_value_t = false)]
    run_keygen: bool,

    // Output ACVP JSON result file for RSA sigGen results.
    #[arg(long)]
    output_siggen: Option<std::path::PathBuf>,

    // Output ACVP JSON result file for ECDSA sigGen results.
    #[arg(long)]
    output_ecdsa_siggen: Option<std::path::PathBuf>,

    // Output ACVP JSON result file for ECDSA keyGen results.
    #[arg(long)]
    output_ecdsa_keygen: Option<std::path::PathBuf>,

    // Output ACVP JSON result file for all EdDSA results (sigVer, sigGen, keyGen).
    #[arg(long)]
    output_eddsa: Option<std::path::PathBuf>,
}

enum AcvpVectors {
    Header {
        url: String,
        vector_set_urls: Vec<String>,
        time: String,
    },
    Aes(aes::AesTestVectorSet),
    Cshake(cshake::CshakeTestVectorSet),
    Ecdsa(ecdsa::EcdsaTestVectorSet),
    EcdsaSigGen(ecdsa::EcdsaSignGenTestVectorSet),
    EcdsaKeyGen(ecdsa::EcdsaKeyGenTestVectorSet),
    Eddsa(eddsa::EddsaTestVectorSet),
    EddsaSigGen(eddsa::EddsaSignGenTestVectorSet),
    EddsaKeyGen(eddsa::EddsaKeygenTestVectorSet),
    Hmac(hmac::HmacTestVectorSet),
    Kmac(kmac::KmacTestVectorSet),
    RsaSigGen(rsa::RsaSignGenTestVectorSet),
    Rsa(rsa::RsaTestVectorSet),
    X25519(x25519::X25519TestVectorSet),
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
    Kmac(kmac::KmacResultVectorSet),
    Cshake(cshake::CshakeResultVectorSet),
    Ecdsa(ecdsa::EcdsaResultVectorSet),
    Eddsa(eddsa::EddsaResultVectorSet),
    RsaSigGen(rsa::RsaSignGenResultVectorSet),
    Rsa(rsa::RsaResultVectorSet),
    X25519(x25519::X25519ResultVectorSet),
    Aes(aes::AesResultVectorSet),
}

fn parse_vector_set(raw: serde_json::Value) -> Result<AcvpVectors> {
    if raw.get("url").is_some() {
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase")]
        struct Header {
            url: String,
            vector_set_urls: Vec<String>,
            time: String,
        }
        let h: Header = serde_json::from_value(raw)?;
        return Ok(AcvpVectors::Header {
            url: h.url,
            vector_set_urls: h.vector_set_urls,
            time: h.time,
        });
    }

    // Extract as owned Strings so `raw` can be moved into serde_json::from_value below.
    let algorithm = raw["algorithm"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("vector set missing 'algorithm' field"))?
        .to_owned();
    let mode = raw
        .get("mode")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_owned();

    Ok(match (algorithm.as_str(), mode.as_str()) {
        (a, _) if a.starts_with("HMAC") => AcvpVectors::Hmac(serde_json::from_value(raw)?),
        (a, _) if a.starts_with("KMAC") => AcvpVectors::Kmac(serde_json::from_value(raw)?),
        (a, _) if a.starts_with("cSHAKE") => AcvpVectors::Cshake(serde_json::from_value(raw)?),
        (a, _) if a.starts_with("ACVP-AES") => AcvpVectors::Aes(serde_json::from_value(raw)?),
        ("ECDSA", "sigVer") => AcvpVectors::Ecdsa(serde_json::from_value(raw)?),
        ("ECDSA", "sigGen") => AcvpVectors::EcdsaSigGen(serde_json::from_value(raw)?),
        ("ECDSA", "keyGen") => AcvpVectors::EcdsaKeyGen(serde_json::from_value(raw)?),
        ("EDDSA", "sigVer") => AcvpVectors::Eddsa(serde_json::from_value(raw)?),
        ("EDDSA", "sigGen") => AcvpVectors::EddsaSigGen(serde_json::from_value(raw)?),
        ("EDDSA", "keyGen") => AcvpVectors::EddsaKeyGen(serde_json::from_value(raw)?),
        ("RSA-sigGen", _) => AcvpVectors::RsaSigGen(serde_json::from_value(raw)?),
        ("RSA-sigVer", _) => AcvpVectors::Rsa(serde_json::from_value(raw)?),
        ("XECDH", _) => AcvpVectors::X25519(serde_json::from_value(raw)?),
        _ => anyhow::bail!("Unknown algorithm/mode: {:?}/{:?}", algorithm, mode),
    })
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

#[allow(clippy::too_many_arguments)]
fn run<R: std::io::Read, W: std::io::Write>(
    opts: &Opts,
    transport: &TransportWrapper,
    input: R,
    expected: Option<R>,
    output: Option<W>,
    output_siggen: Option<W>,
    output_eddsa: Option<W>,
    output_ecdsa_siggen: Option<W>,
    output_ecdsa_keygen: Option<W>,
) -> Result<()> {
    let spi = transport.spi("BOOTSTRAP")?;
    let spi_console_device = SpiConsoleDevice::new(&*spi, None, /*ignore_frame_num=*/ false)?;
    let _ = UartConsole::wait_for(&spi_console_device, r"Running ", opts.timeout)?;

    let raw_vectors: Vec<serde_json::Value> = deser_hjson::from_reader(input)?;
    let acvp_vectors = raw_vectors
        .into_iter()
        .map(parse_vector_set)
        .collect::<Result<Vec<_>>>()?;
    let mut acvp_results: Vec<AcvpResults> = Vec::with_capacity(acvp_vectors.len());
    // All EdDSA results (sigVer, sigGen, keyGen) are collected for --output-eddsa.
    let mut eddsa_results: Vec<serde_json::Value> = Vec::new();
    // RSA sigGen results are serialised to --output-siggen.
    // They are never compared against --expected.
    let mut siggen_results: Vec<serde_json::Value> = Vec::new();
    // ECDSA sigGen results are serialised to --output-ecdsa-siggen.
    let mut ecdsa_siggen_results: Vec<serde_json::Value> = Vec::new();
    // ECDSA keyGen results are serialised to --output-ecdsa-keygen.
    let mut ecdsa_keygen_results: Vec<serde_json::Value> = Vec::new();

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
            AcvpVectors::Kmac(vs) => {
                acvp_results.push(AcvpResults::Kmac(kmac::run_kmac_vector_set(
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
            AcvpVectors::Ecdsa(vs) => {
                if opts.expected.is_some() || opts.output.is_some() {
                    acvp_results.push(AcvpResults::Ecdsa(ecdsa::run_ecdsa_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?));
                }
            }
            AcvpVectors::EcdsaSigGen(vs) => {
                if opts.run_siggen || opts.output_ecdsa_siggen.is_some() {
                    let result = ecdsa::run_ecdsa_siggen_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?;
                    ecdsa_siggen_results.push(serde_json::to_value(result)?);
                }
            }
            AcvpVectors::EcdsaKeyGen(vs) => {
                if opts.run_keygen || opts.output_ecdsa_keygen.is_some() {
                    let result =
                        ecdsa::run_ecdsa_keygen_vector_set(opts.timeout, &spi_console_device, &vs)?;
                    ecdsa_keygen_results.push(serde_json::to_value(result)?);
                }
            }
            AcvpVectors::Eddsa(vs) => {
                if opts.expected.is_some() || opts.output.is_some() {
                    let result = eddsa::run_eddsa_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?;
                    eddsa_results.push(serde_json::to_value(&result)?);
                    acvp_results.push(AcvpResults::Eddsa(result));
                }
            }
            AcvpVectors::EddsaSigGen(vs) => {
                if opts.run_siggen {
                    let result = eddsa::run_eddsa_siggen_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?;
                    eddsa_results.push(serde_json::to_value(result)?);
                }
            }
            AcvpVectors::EddsaKeyGen(vs) => {
                if opts.run_keygen {
                    let result =
                        eddsa::run_eddsa_keygen_vector_set(opts.timeout, &spi_console_device, &vs)?;
                    eddsa_results.push(serde_json::to_value(result)?);
                }
            }
            AcvpVectors::RsaSigGen(vs) => {
                if opts.run_siggen || opts.output_siggen.is_some() {
                    let result = rsa::run_rsa_siggen_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?;
                    siggen_results.push(serde_json::to_value(result)?);
                }
            }
            AcvpVectors::Rsa(vs) => {
                if opts.expected.is_some() || opts.output.is_some() {
                    acvp_results.push(AcvpResults::Rsa(rsa::run_rsa_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?));
                }
            }
            AcvpVectors::X25519(vs) => {
                acvp_results.push(AcvpResults::X25519(x25519::run_x25519_vector_set(
                    opts.timeout,
                    &spi_console_device,
                    &vs,
                )?));
            }
            AcvpVectors::Aes(vs) => {
                if opts.expected.is_some() || opts.output.is_some() {
                    acvp_results.push(AcvpResults::Aes(aes::run_aes_vector_set(
                        opts.timeout,
                        &spi_console_device,
                        &vs,
                        opts.skip_stride,
                        opts.seed,
                    )?));
                }
            }
        }
    }
    if let Some(w) = output {
        serde_json::to_writer_pretty(w, &acvp_results)?;
    }
    if let Some(w) = output_siggen {
        serde_json::to_writer_pretty(w, &siggen_results)?;
    }
    if let Some(w) = output_ecdsa_siggen {
        serde_json::to_writer_pretty(w, &ecdsa_siggen_results)?;
    }
    if let Some(w) = output_ecdsa_keygen {
        serde_json::to_writer_pretty(w, &ecdsa_keygen_results)?;
    }
    if let Some(w) = output_eddsa {
        serde_json::to_writer_pretty(w, &eddsa_results)?;
    }
    if let Some(r) = expected {
        let expected_results_json: serde_json::Value = deser_hjson::from_reader(r)?;
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
    if opts.expected.is_none()
        && opts.output.is_none()
        && !opts.run_siggen
        && !opts.run_keygen
        && opts.output_siggen.is_none()
        && opts.output_ecdsa_siggen.is_none()
        && opts.output_ecdsa_keygen.is_none()
        && opts.output_eddsa.is_none()
    {
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
    let output_siggen = match &opts.output_siggen {
        Some(path) => {
            let f = std::fs::File::create(path)
                .inspect_err(|e| log::error!("open siggen output file: {e}"))?;
            Some(std::io::BufWriter::new(f))
        }
        None => None,
    };
    let output_eddsa = match &opts.output_eddsa {
        Some(path) => {
            let f = std::fs::File::create(path)
                .inspect_err(|e| log::error!("open eddsa output file: {e}"))?;
            Some(std::io::BufWriter::new(f))
        }
        None => None,
    };
    let output_ecdsa_siggen = match &opts.output_ecdsa_siggen {
        Some(path) => {
            let f = std::fs::File::create(path)
                .inspect_err(|e| log::error!("open ecdsa siggen output file: {e}"))?;
            Some(std::io::BufWriter::new(f))
        }
        None => None,
    };
    let output_ecdsa_keygen = match &opts.output_ecdsa_keygen {
        Some(path) => {
            let f = std::fs::File::create(path)
                .inspect_err(|e| log::error!("open ecdsa keygen output file: {e}"))?;
            Some(std::io::BufWriter::new(f))
        }
        None => None,
    };
    run(
        &opts,
        &transport,
        input,
        expected,
        output,
        output_siggen,
        output_eddsa,
        output_ecdsa_siggen,
        output_ecdsa_keygen,
    )
}
