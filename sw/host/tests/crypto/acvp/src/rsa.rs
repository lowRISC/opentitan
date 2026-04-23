// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::cmp::min;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::rsa_commands::{
    CryptotestRsaVerify, CryptotestRsaVerifyResp, RsaSubcommand,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

// OpenTitan uJSON allocates 514 bytes for these arrays
const RSA_MAX_BYTES: usize = 512;
const RSA_MAX_MSG_BYTES: usize = 514;

// Hashing algorithm IDs matching your C firmware (as usize)
const HASH_SHA256: usize = 0;
const HASH_SHA384: usize = 1;
const HASH_SHA512: usize = 2;
const HASH_SHA3_256: usize = 3;
const HASH_SHA3_384: usize = 4;
const HASH_SHA3_512: usize = 5;

// Padding mode IDs matching your C firmware (as usize)
const PADDING_PKCS: usize = 0;
const PADDING_PSS: usize = 1;
const PADDING_OAEP: usize = 2;

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct RsaTestCase {
    tc_id: usize,
    #[serde(default)]
    n: Option<String>,
    #[serde(default)]
    e: Option<String>,
    #[serde(default)]
    d: Option<String>,
    #[serde(default)]
    msg: Option<String>,
    #[serde(default)]
    sig: Option<String>,
    #[serde(default)]
    pt: Option<String>,
    #[serde(default)]
    ct: Option<String>,
    #[serde(default)]
    label: Option<String>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct RsaTestGroup {
    tg_id: usize,
    test_type: String,
    modulo: usize, // e.g., 2048, 3072, 4096
    hash_alg: String,
    #[serde(default)]
    sig_type: Option<String>,
    tests: Vec<RsaTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<RsaTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaResultCase {
    pub tc_id: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub test_passed: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ct: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pt: Option<String>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaResultGroup {
    pub tg_id: usize,
    pub tests: Vec<RsaResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<RsaResultGroup>,
}

fn map_hash_alg(alg: &str) -> Result<usize> {
    match alg.to_uppercase().as_str() {
        "SHA-256" | "SHA2-256" => Ok(HASH_SHA256),
        "SHA-384" | "SHA2-384" => Ok(HASH_SHA384),
        "SHA-512" | "SHA2-512" => Ok(HASH_SHA512),
        "SHA3-256" => Ok(HASH_SHA3_256),
        "SHA3-384" => Ok(HASH_SHA3_384),
        "SHA3-512" => Ok(HASH_SHA3_512),
        _ => Err(std::io::Error::from(std::io::ErrorKind::InvalidInput).into()),
    }
}

fn run_rsa_verify_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &RsaTestGroup,
    tc: &RsaTestCase,
    padding: usize,
    hashing: usize,
) -> Result<RsaResultCase> {
    // OpenTitan expects little-endian integers for math, so we reverse `n` and `sig`
    let mut n = Vec::<u8>::from_hex(tc.n.as_ref().unwrap())?;
    n.reverse();

    let mut sig = Vec::<u8>::from_hex(tc.sig.as_ref().unwrap())?;
    sig.reverse();

    // The message is just a byte string, so we do NOT reverse it.
    let msg = Vec::<u8>::from_hex(tc.msg.as_ref().unwrap())?;

    // Convert hex exponent (e.g. "010001") to u32
    let e_bytes = Vec::<u8>::from_hex(tc.e.as_ref().unwrap())?;
    let mut e: u32 = 0;
    for &b in &e_bytes {
        e = (e << 8) | (b as u32);
    }

    let mut n_array = arrayvec::ArrayVec::<u8, RSA_MAX_BYTES>::new();
    n_array.try_extend_from_slice(&n)?;

    let mut msg_array = arrayvec::ArrayVec::<u8, RSA_MAX_MSG_BYTES>::new();
    msg_array.try_extend_from_slice(&msg)?;

    let mut sig_array = arrayvec::ArrayVec::<u8, RSA_MAX_MSG_BYTES>::new();
    sig_array.try_extend_from_slice(&sig)?;

    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaVerify.send(spi_console)?;

    CryptotestRsaVerify {
        padding,
        security_level: tg.modulo, // Now properly typed as usize
        hashing,
        e,
        n: n_array,
        sig_len: sig.len(),
        sig: sig_array,
        msg_len: msg.len(),
        msg: msg_array,
    }
    .send(spi_console)?;

    let resp = CryptotestRsaVerifyResp::recv(spi_console, timeout, false, false)?;

    Ok(RsaResultCase {
        tc_id: tc.tc_id,
        test_passed: Some(resp.result),
        ct: None,
        pt: None,
    })
}

fn run_rsa_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &str,
    tg: &RsaTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<RsaResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    let mut result_cases = Vec::new();

    let hashing = map_hash_alg(&tg.hash_alg)?;

    let padding = match tg
        .sig_type
        .as_deref()
        .unwrap_or("pkcs1v15")
        .to_lowercase()
        .as_str()
    {
        "pss" => PADDING_PSS,
        "oaep" => PADDING_OAEP,
        _ => PADDING_PKCS,
    };

    // Ensure that at least one test per group is run
    let stride = min(skip_stride, tg.tests.len());

    // Prevent division by zero if a test group happens to be entirely empty
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            // Skip test
            continue;
        }

        log::info!("tc_id: {}", tc.tc_id);

        if algorithm.contains("sigVer") {
            result_cases.push(run_rsa_verify_case(
                timeout,
                spi_console,
                tg,
                tc,
                padding,
                hashing,
            )?);
        } else {
            return Err(std::io::Error::other(format!(
                "Algorithm {} not implemented in harness",
                algorithm
            ))
            .into());
        }
    }
    Ok(RsaResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_rsa_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &RsaTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<RsaResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let seed = seed_arg.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    // Create a deterministic RNG from the seed for skipping
    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(skip_stride_arg)
    {
        Some(offset) => (skip_stride_arg, offset),
        // if skip_stride_arg is 0, skip_stride is set to 1 to execute all the tests
        None => (1usize, 0usize),
    };

    let mut result_groups = Vec::with_capacity(vs.test_groups.len());

    for tg in &vs.test_groups {
        result_groups.push(run_rsa_group(
            timeout,
            spi_console,
            &vs.algorithm,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(RsaResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
