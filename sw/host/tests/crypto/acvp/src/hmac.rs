// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::cmp::min;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;

use cryptotest_commands::hmac_commands::{
    CryptotestHmacHashAlg, CryptotestHmacKey, CryptotestHmacMessage, CryptotestHmacTag,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

// NIST ACVP JSON schema definitions
// Test vectors: https://pages.nist.gov/ACVP/draft-fussell-acvp-mac.html#name-hmac-test-vectors
// Test results: https://pages.nist.gov/ACVP/draft-fussell-acvp-mac.html#name-hmac-test-vector-responses

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct HmacTestCase {
    tc_id: usize,
    key: String,
    msg: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct HmacTestGroup {
    tg_id: usize,
    test_type: String,
    key_len: usize,
    msg_len: usize,
    mac_len: usize,
    tests: Vec<HmacTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct HmacTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<HmacTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct HmacResultCase {
    pub tc_id: usize,
    pub mac: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct HmacResultGroup {
    pub tg_id: usize,
    pub tests: Vec<HmacResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct HmacResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<HmacResultGroup>,
}

fn run_hmac_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &CryptotestHmacHashAlg,
    mac_len: usize,
    tc: &HmacTestCase,
) -> Result<HmacResultCase> {
    log::info!("tc_id: {}", tc.tc_id);
    let key = Vec::<u8>::from_hex(tc.key.as_bytes())?;
    let msg = Vec::<u8>::from_hex(tc.msg.as_bytes())?;

    CryptotestCommand::Hmac.send(spi_console)?;
    algorithm.send(spi_console)?;
    CryptotestHmacKey {
        key: arrayvec::ArrayVec::try_from(key.as_slice()).unwrap(),
        key_len: key.len(),
    }
    .send(spi_console)?;

    CryptotestHmacMessage {
        message: arrayvec::ArrayVec::try_from(msg.as_slice()).unwrap(),
        message_len: msg.len(),
    }
    .send(spi_console)?;

    let hmac_output = CryptotestHmacTag::recv(spi_console, timeout, false, false)?;

    let returned_bits = hmac_output.tag[..std::cmp::min(mac_len / 8, hmac_output.tag_len)]
        .iter()
        .try_fold(String::new(), |mut acc, w| {
            core::fmt::write(&mut acc, core::format_args!("{:02x}", w))
                .or(Err(std::io::Error::from(std::io::ErrorKind::Other)))?;
            Ok::<String, std::io::Error>(acc)
        })?;

    Ok(HmacResultCase {
        tc_id: tc.tc_id,
        mac: returned_bits,
    })
}

fn run_hmac_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &CryptotestHmacHashAlg,
    tg: &HmacTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<HmacResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    let mut result_cases: Vec<HmacResultCase> = Vec::new();

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

        result_cases.push(run_hmac_case(
            timeout,
            spi_console,
            algorithm,
            tg.mac_len,
            tc,
        )?);
    }
    Ok(HmacResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_hmac_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &HmacTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<HmacResultVectorSet> {
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

    let mut result_groups: Vec<HmacResultGroup> = Vec::with_capacity(vs.test_groups.len());
    let algorithm = match vs.algorithm.as_str() {
        "HMAC-SHA2-256" => CryptotestHmacHashAlg::Sha256,
        "HMAC-SHA2-384" => CryptotestHmacHashAlg::Sha384,
        "HMAC-SHA2-512" => CryptotestHmacHashAlg::Sha512,
        _ => return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput).into()),
    };

    for tg in &vs.test_groups {
        result_groups.push(run_hmac_group(
            timeout,
            spi_console,
            &algorithm,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(HmacResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
