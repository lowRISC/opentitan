// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::kmac_commands::{
    CryptotestKmacCustomizationString, CryptotestKmacKey, CryptotestKmacMessage,
    CryptotestKmacMode, CryptotestKmacRequiredTagLength, CryptotestKmacTag,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

// NIST ACVP JSON schema definitions
// Test vectors: https://pages.nist.gov/ACVP/draft-celi-acvp-kmac.html#name-test-vectors
// Test results: https://pages.nist.gov/ACVP/draft-celi-acvp-kmac.html#name-test-vector-responses

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct KmacTestCase {
    tc_id: usize,
    key: String,
    key_len: usize,
    msg: String,
    msg_len: usize,
    mac_len: usize,
    #[serde(default)]
    customization: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct KmacTestGroup {
    tg_id: usize,
    test_type: String,
    xof: bool,
    tests: Vec<KmacTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct KmacTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<KmacTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct KmacResultCase {
    pub tc_id: usize,
    pub mac: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct KmacResultGroup {
    pub tg_id: usize,
    pub tests: Vec<KmacResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct KmacResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<KmacResultGroup>,
}

fn run_kmac_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    mode: &CryptotestKmacMode,
    tc: &KmacTestCase,
) -> Result<KmacResultCase> {
    log::info!("tc_id: {}", tc.tc_id);

    let key = Vec::<u8>::from_hex(tc.key.as_bytes())?;
    let msg = Vec::<u8>::from_hex(tc.msg.as_bytes())?;
    let cust_str = tc.customization.as_bytes().to_vec();

    let mac_bytes = (tc.mac_len + 7) / 8;
    // Firmware divides required_tag_length by sizeof(uint32_t) to size the tag
    // buffer, so it must be word-aligned.
    let mac_bytes_aligned = (mac_bytes + 3) & !3;

    CryptotestCommand::Kmac.send(spi_console)?;
    mode.send(spi_console)?;

    CryptotestKmacRequiredTagLength {
        required_tag_length: mac_bytes_aligned,
    }
    .send(spi_console)?;

    CryptotestKmacKey {
        key: ArrayVec::try_from(key.as_slice()).unwrap(),
        key_len: key.len(),
    }
    .send(spi_console)?;

    CryptotestKmacMessage {
        message: ArrayVec::try_from(msg.as_slice()).unwrap(),
        message_len: msg.len(),
    }
    .send(spi_console)?;

    CryptotestKmacCustomizationString {
        customization_string: ArrayVec::try_from(cust_str.as_slice()).unwrap(),
        customization_string_len: cust_str.len(),
    }
    .send(spi_console)?;

    let kmac_output = CryptotestKmacTag::recv(spi_console, timeout, false, false)?;
    let mac_hex = hex::encode(&kmac_output.tag[..mac_bytes]);

    Ok(KmacResultCase {
        tc_id: tc.tc_id,
        mac: mac_hex,
    })
}

fn run_kmac_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    mode: &CryptotestKmacMode,
    tg: &KmacTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<KmacResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    if tg.xof {
        return Err(std::io::Error::other(format!(
            "tg_id {}: XOF mode is not supported by the OpenTitan KMAC HWIP",
            tg.tg_id
        ))
        .into());
    }

    let mut result_cases: Vec<KmacResultCase> = Vec::new();

    let stride = skip_stride.min(tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        result_cases.push(run_kmac_case(timeout, spi_console, mode, tc)?);
    }

    Ok(KmacResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_kmac_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &KmacTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<KmacResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let seed = seed_arg.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(skip_stride_arg)
    {
        Some(offset) => (skip_stride_arg, offset),
        None => (1usize, 0usize),
    };

    let mode = match vs.algorithm.as_str() {
        "KMAC-128" => CryptotestKmacMode::Kmac128,
        "KMAC-256" => CryptotestKmacMode::Kmac256,
        _ => return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput).into()),
    };

    let mut result_groups: Vec<KmacResultGroup> = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_kmac_group(
            timeout,
            spi_console,
            &mode,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(KmacResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
