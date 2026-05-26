// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::cmp::min;
use std::time::Duration;

use cryptotest_commands::aes_commands::{
    AesSubcommand, CryptotestAesData, CryptotestAesMode, CryptotestAesOperation,
    CryptotestAesOutput, CryptotestAesPadding,
};
use cryptotest_commands::aes_gcm_commands::{
    AesGcmSubcommand, CryptotestAesGcmData, CryptotestAesGcmOperation, CryptotestAesGcmOutput,
};
use cryptotest_commands::commands::CryptotestCommand;

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

const AES_BLOCK_BYTES: usize = 16;
const AES_CMD_MAX_KEY_BYTES: usize = 32;
const AES_CMD_MAX_MSG_BYTES: usize = 64;
const AES_GCM_CMD_MAX_MSG_BYTES: usize = 64;
const AES_GCM_CMD_MAX_TAG_BYTES: usize = 16;

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct AesTestCase {
    tc_id: usize,
    key: String,
    #[serde(default)]
    pt: String,
    #[serde(default)]
    ct: String,
    #[serde(default)]
    iv: String,
    #[serde(default)]
    aad: String,
    #[serde(default)]
    tag: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct AesTestGroup {
    tg_id: usize,
    test_type: String,
    direction: String,
    key_len: usize,
    #[serde(default)]
    iv_len: usize,
    #[serde(default)]
    aad_len: usize,
    #[serde(default)]
    tag_len: usize,
    tests: Vec<AesTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AesTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<AesTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AesResultCase {
    pub tc_id: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ct: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pt: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tag: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub test_passed: Option<bool>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AesResultGroup {
    pub tg_id: usize,
    pub tests: Vec<AesResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AesResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<AesResultGroup>,
}

fn run_aes_block_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &str,
    direction: &str,
    tc: &AesTestCase,
) -> Result<AesResultCase> {
    log::info!("tc_id: {}", tc.tc_id);

    let key = Vec::<u8>::from_hex(tc.key.as_bytes())?;
    let input_hex = if direction == "encrypt" {
        &tc.pt
    } else {
        &tc.ct
    };
    let input_bytes = Vec::<u8>::from_hex(input_hex.as_bytes())?;

    let mut iv = [0u8; AES_BLOCK_BYTES];
    if !tc.iv.is_empty() {
        let iv_bytes = Vec::<u8>::from_hex(tc.iv.as_bytes())?;
        let copy_len = min(iv_bytes.len(), AES_BLOCK_BYTES);
        iv[..copy_len].copy_from_slice(&iv_bytes[..copy_len]);
    }

    let mode = match algorithm {
        "ACVP-AES-ECB" => CryptotestAesMode::Ecb,
        "ACVP-AES-CBC" => CryptotestAesMode::Cbc,
        "ACVP-AES-CFB128" => CryptotestAesMode::Cfb,
        "ACVP-AES-OFB" => CryptotestAesMode::Ofb,
        "ACVP-AES-CTR" => CryptotestAesMode::Ctr,
        _ => anyhow::bail!("Unsupported AES algorithm: {}", algorithm),
    };
    let operation = if direction == "encrypt" {
        CryptotestAesOperation::Encrypt
    } else {
        CryptotestAesOperation::Decrypt
    };

    CryptotestCommand::Aes.send(spi_console)?;
    AesSubcommand::AesBlock.send(spi_console)?;
    mode.send(spi_console)?;
    operation.send(spi_console)?;
    CryptotestAesPadding::Null.send(spi_console)?;

    let mut key_arr: ArrayVec<u8, AES_CMD_MAX_KEY_BYTES> = ArrayVec::new();
    key_arr.try_extend_from_slice(&key)?;
    let mut input_arr: ArrayVec<u8, AES_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    input_arr.try_extend_from_slice(&input_bytes)?;

    CryptotestAesData {
        key: key_arr,
        key_length: key.len(),
        iv: ArrayVec::from(iv),
        input: input_arr,
        input_len: input_bytes.len(),
    }
    .send(spi_console)?;

    let aes_output = CryptotestAesOutput::recv(spi_console, timeout, false, false)?;
    let output_len = aes_output.output_len as usize;
    let output_hex = hex::encode_upper(&aes_output.output[..output_len]);

    if direction == "encrypt" {
        Ok(AesResultCase {
            tc_id: tc.tc_id,
            ct: Some(output_hex),
            pt: None,
            tag: None,
            test_passed: None,
        })
    } else {
        Ok(AesResultCase {
            tc_id: tc.tc_id,
            ct: None,
            pt: Some(output_hex),
            tag: None,
            test_passed: None,
        })
    }
}

fn run_aes_gcm_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    direction: &str,
    tag_len_bits: usize,
    tc: &AesTestCase,
) -> Result<AesResultCase> {
    log::info!("tc_id: {}", tc.tc_id);

    let key = Vec::<u8>::from_hex(tc.key.as_bytes())?;
    let iv_bytes = Vec::<u8>::from_hex(tc.iv.as_bytes())?;
    let aad_bytes = if tc.aad.is_empty() {
        vec![]
    } else {
        Vec::<u8>::from_hex(tc.aad.as_bytes())?
    };
    let tag_len_bytes = tag_len_bits / 8;

    let (input_bytes, tag_bytes) = if direction == "encrypt" {
        let pt = if tc.pt.is_empty() {
            vec![]
        } else {
            Vec::<u8>::from_hex(tc.pt.as_bytes())?
        };
        // Send zeros of the right tag length; the firmware computes and returns the actual tag.
        (pt, vec![0u8; tag_len_bytes])
    } else {
        let ct = if tc.ct.is_empty() {
            vec![]
        } else {
            Vec::<u8>::from_hex(tc.ct.as_bytes())?
        };
        let tag = Vec::<u8>::from_hex(tc.tag.as_bytes())?;
        (ct, tag)
    };

    CryptotestCommand::AesGcm.send(spi_console)?;
    AesGcmSubcommand::AesGcmOp.send(spi_console)?;

    let operation = if direction == "encrypt" {
        CryptotestAesGcmOperation::Encrypt
    } else {
        CryptotestAesGcmOperation::Decrypt
    };
    operation.send(spi_console)?;

    let mut key_arr: ArrayVec<u8, AES_CMD_MAX_KEY_BYTES> = ArrayVec::new();
    key_arr.try_extend_from_slice(&key)?;
    let mut iv_arr: ArrayVec<u8, AES_BLOCK_BYTES> = ArrayVec::new();
    iv_arr.try_extend_from_slice(&iv_bytes)?;
    let mut input_arr: ArrayVec<u8, AES_GCM_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    input_arr.try_extend_from_slice(&input_bytes)?;
    let mut aad_arr: ArrayVec<u8, AES_GCM_CMD_MAX_MSG_BYTES> = ArrayVec::new();
    aad_arr.try_extend_from_slice(&aad_bytes)?;
    let mut tag_arr: ArrayVec<u8, AES_GCM_CMD_MAX_TAG_BYTES> = ArrayVec::new();
    tag_arr.try_extend_from_slice(&tag_bytes)?;

    CryptotestAesGcmData {
        key: key_arr,
        key_length: key.len(),
        iv: iv_arr,
        iv_length: iv_bytes.len(),
        input: input_arr,
        input_length: input_bytes.len(),
        aad: aad_arr,
        aad_length: aad_bytes.len(),
        tag: tag_arr,
        tag_length: tag_len_bytes,
    }
    .send(spi_console)?;

    let gcm_output = CryptotestAesGcmOutput::recv(spi_console, timeout, false, false)?;

    if direction == "encrypt" {
        let ct_hex = hex::encode_upper(&gcm_output.output[..gcm_output.output_len]);
        let tag_hex = hex::encode_upper(&gcm_output.tag[..gcm_output.tag_len]);
        Ok(AesResultCase {
            tc_id: tc.tc_id,
            ct: Some(ct_hex),
            pt: None,
            tag: Some(tag_hex),
            test_passed: None,
        })
    } else if gcm_output.tag_valid {
        let pt_hex = hex::encode_upper(&gcm_output.output[..gcm_output.output_len]);
        Ok(AesResultCase {
            tc_id: tc.tc_id,
            ct: None,
            pt: Some(pt_hex),
            tag: None,
            test_passed: None,
        })
    } else {
        Ok(AesResultCase {
            tc_id: tc.tc_id,
            ct: None,
            pt: None,
            tag: None,
            test_passed: Some(false),
        })
    }
}

fn run_aes_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &str,
    tg: &AesTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<AesResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    let mut result_cases: Vec<AesResultCase> = Vec::new();

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    let is_gcm = algorithm == "ACVP-AES-GCM";
    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        let result = if is_gcm {
            run_aes_gcm_case(timeout, spi_console, &tg.direction, tg.tag_len, tc)?
        } else {
            run_aes_block_case(timeout, spi_console, algorithm, &tg.direction, tc)?
        };
        result_cases.push(result);
    }

    Ok(AesResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_aes_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &AesTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<AesResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let seed = seed_arg.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(skip_stride_arg)
    {
        Some(offset) => (skip_stride_arg, offset),
        None => (1usize, 0usize),
    };

    let mut result_groups: Vec<AesResultGroup> = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_aes_group(
            timeout,
            spi_console,
            &vs.algorithm,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(AesResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
