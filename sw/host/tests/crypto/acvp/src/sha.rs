// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::cmp::min;
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::sha_commands::{
    CryptotestShaInput, CryptotestShaMode, CryptotestShaOutput,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

const SHA_CMD_MAX_MSG_BYTES: usize = 256;

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShaTestCase {
    tc_id: usize,
    len: usize,
    msg: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct ShaTestGroup {
    tg_id: usize,
    test_type: String,
    tests: Vec<ShaTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ShaTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<ShaTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ShaResultCase {
    pub tc_id: usize,
    pub md: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ShaResultGroup {
    pub tg_id: usize,
    pub tests: Vec<ShaResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ShaResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<ShaResultGroup>,
}

fn run_sha_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    mode: &CryptotestShaMode,
    tc: &ShaTestCase,
) -> Result<ShaResultCase> {
    log::info!("tc_id: {}", tc.tc_id);

    // `len` is in bits; we only retain byte-aligned vectors so len/8 is exact.
    let msg_len_bytes = tc.len / 8;
    let msg_bytes: Vec<u8> = if msg_len_bytes == 0 {
        vec![]
    } else {
        let full = Vec::<u8>::from_hex(tc.msg.as_bytes())?;
        full[..msg_len_bytes].to_vec()
    };

    CryptotestCommand::Sha.send(spi_console)?;
    mode.send(spi_console)?;

    let mut msg_arr: ArrayVec<u8, SHA_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    msg_arr.try_extend_from_slice(&msg_bytes)?;

    CryptotestShaInput {
        msg: msg_arr,
        msg_len: msg_len_bytes as u32,
    }
    .send(spi_console)?;

    let output = CryptotestShaOutput::recv(spi_console, timeout, false, false)?;
    let digest_len = output.digest_len as usize;
    let md = hex::encode_upper(&output.digest[..digest_len]);

    Ok(ShaResultCase {
        tc_id: tc.tc_id,
        md,
    })
}

fn run_sha_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    mode: &CryptotestShaMode,
    tg: &ShaTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<ShaResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    let mut result_cases: Vec<ShaResultCase> = Vec::new();

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        result_cases.push(run_sha_case(timeout, spi_console, mode, tc)?);
    }

    Ok(ShaResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_sha_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &ShaTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<ShaResultVectorSet> {
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
        "SHA2-256" => CryptotestShaMode::SHA2_256,
        "SHA2-384" => CryptotestShaMode::SHA2_384,
        "SHA2-512" => CryptotestShaMode::SHA2_512,
        "SHA3-224" => CryptotestShaMode::SHA3_224,
        "SHA3-256" => CryptotestShaMode::SHA3_256,
        "SHA3-384" => CryptotestShaMode::SHA3_384,
        "SHA3-512" => CryptotestShaMode::SHA3_512,
        _ => anyhow::bail!("Unsupported SHA algorithm: {}", vs.algorithm),
    };

    let mut result_groups: Vec<ShaResultGroup> = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_sha_group(
            timeout,
            spi_console,
            &mode,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(ShaResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
