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
    CryptotestRsaKeygen, CryptotestRsaKeygenResp, CryptotestRsaSign, CryptotestRsaSignResp,
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

// Hashing algorithm IDs matching the C firmware
const HASH_SHA256: usize = 0;
const HASH_SHA384: usize = 1;
const HASH_SHA512: usize = 2;
const HASH_SHA3_256: usize = 3;
const HASH_SHA3_384: usize = 4;
const HASH_SHA3_512: usize = 5;

// Padding mode IDs matching the C firmware
const PADDING_PKCS: usize = 0;
const PADDING_PSS: usize = 1;
const PADDING_OAEP: usize = 2;

// Signature verification input structs

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
    modulo: usize,
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

// Signature verification result structs

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

// Signature generation input structs

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct RsaSignGenTestCase {
    tc_id: usize,
    message: String,
    #[serde(default)]
    deferred: bool,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct RsaSignGenTestGroup {
    tg_id: usize,
    test_type: String,
    modulo: usize,
    hash_alg: String,
    #[serde(default)]
    sig_type: Option<String>,
    tests: Vec<RsaSignGenTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaSignGenTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<RsaSignGenTestGroup>,
}

// Signature generation result structs

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaSignGenResultCase {
    pub tc_id: usize,
    pub signature: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaSignGenResultGroup {
    pub tg_id: usize,
    pub n: String,
    pub e: String,
    pub tests: Vec<RsaSignGenResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RsaSignGenResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<RsaSignGenResultGroup>,
}

// Helper functions

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

fn map_padding(sig_type: Option<&str>) -> usize {
    match sig_type.unwrap_or("pkcs1v1.5").to_lowercase().as_str() {
        "pss" => PADDING_PSS,
        "oaep" => PADDING_OAEP,
        _ => PADDING_PKCS,
    }
}

fn u32_to_be_hex(v: u32) -> String {
    let bytes = v.to_be_bytes();
    let significant = bytes.iter().skip_while(|&&b| b == 0);
    let vec: Vec<u8> = significant.copied().collect();
    let hex = hex::encode_upper(&vec);
    // ensure even length
    if hex.len() % 2 == 1 {
        format!("0{}", hex)
    } else {
        hex
    }
}

// Signature Verification

fn run_rsa_verify_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &RsaTestGroup,
    tc: &RsaTestCase,
    padding: usize,
    hashing: usize,
) -> Result<RsaResultCase> {
    // OpenTitan uses little-endian integers; reverse `n` and `sig`.
    let mut n = Vec::<u8>::from_hex(tc.n.as_ref().unwrap())?;
    n.reverse();

    let mut sig = Vec::<u8>::from_hex(tc.sig.as_ref().unwrap())?;
    sig.reverse();

    let msg = Vec::<u8>::from_hex(tc.msg.as_ref().unwrap())?;

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
        security_level: tg.modulo,
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
    let padding = map_padding(tg.sig_type.as_deref());

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
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

    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(skip_stride_arg)
    {
        Some(offset) => (skip_stride_arg, offset),
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

// Signature Generation

// Runs key generation on the device
fn run_rsa_keygen(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    security_level: usize,
    padding: usize,
) -> Result<(Vec<u8>, Vec<u8>, u32)> {
    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaKeygen.send(spi_console)?;

    CryptotestRsaKeygen {
        security_level,
        padding,
    }
    .send(spi_console)?;

    let resp = CryptotestRsaKeygenResp::recv(spi_console, timeout, false, false)?;

    // Convert to little-endian.
    let n_le = resp.n.as_slice()[..resp.n_len].to_vec();
    let d_le = resp.d.as_slice()[..resp.d_len].to_vec();

    Ok((n_le, d_le, resp.e))
}

// Signs `tc.message` with the provided key, verifies the resulting signature,
// and returns the test result case with the signature.
#[allow(clippy::too_many_arguments)]
fn run_rsa_sign_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    security_level: usize,
    padding: usize,
    hashing: usize,
    n_le: &[u8],
    d_le: &[u8],
    e: u32,
    tc: &RsaSignGenTestCase,
) -> Result<RsaSignGenResultCase> {
    let msg = Vec::<u8>::from_hex(&tc.message)?;

    let mut n_array = arrayvec::ArrayVec::<u8, RSA_MAX_BYTES>::new();
    n_array.try_extend_from_slice(n_le)?;

    let mut d_array = arrayvec::ArrayVec::<u8, RSA_MAX_BYTES>::new();
    d_array.try_extend_from_slice(d_le)?;

    let mut msg_array = arrayvec::ArrayVec::<u8, RSA_MAX_MSG_BYTES>::new();
    msg_array.try_extend_from_slice(&msg)?;

    let label_array = arrayvec::ArrayVec::<u8, RSA_MAX_MSG_BYTES>::new();

    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaSign.send(spi_console)?;

    CryptotestRsaSign {
        msg: msg_array.clone(),
        msg_len: msg.len(),
        e,
        d: d_array,
        n: n_array.clone(),
        security_level,
        label: label_array,
        label_len: 0,
        hashing,
        padding,
    }
    .send(spi_console)?;

    let sign_resp = CryptotestRsaSignResp::recv(spi_console, timeout, false, false)?;

    let sig_len = sign_resp.signature_len;
    let sig_le = sign_resp.signature.as_slice()[..sig_len].to_vec();

    // Verify the signature we just produced.
    let mut sig_array = arrayvec::ArrayVec::<u8, RSA_MAX_MSG_BYTES>::new();
    sig_array.try_extend_from_slice(&sig_le)?;

    CryptotestCommand::Rsa.send(spi_console)?;
    RsaSubcommand::RsaVerify.send(spi_console)?;

    CryptotestRsaVerify {
        msg: msg_array,
        msg_len: msg.len(),
        e,
        n: n_array,
        security_level,
        sig: sig_array,
        sig_len,
        hashing,
        padding,
    }
    .send(spi_console)?;

    let verify_resp = CryptotestRsaVerifyResp::recv(spi_console, timeout, false, false)?;

    if !verify_resp.result {
        return Err(std::io::Error::other(format!(
            "Sign-then-verify failed for tc_id {}",
            tc.tc_id
        ))
        .into());
    }

    // ACVP output uses big-endian hex for the signature.
    let mut sig_be = sig_le;
    sig_be.reverse();

    Ok(RsaSignGenResultCase {
        tc_id: tc.tc_id,
        signature: hex::encode_upper(&sig_be),
    })
}

fn run_rsa_siggen_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &RsaSignGenTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<RsaSignGenResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    let hashing = map_hash_alg(&tg.hash_alg)?;
    let padding = map_padding(tg.sig_type.as_deref());

    // One key generation per group; all test cases in the group reuse the key.
    let (n_le, d_le, e) = run_rsa_keygen(timeout, spi_console, tg.modulo, padding)?;

    // Convert n and e to big-endian hex for the ACVP result.
    let mut n_be = n_le.clone();
    n_be.reverse();
    let n_hex = hex::encode_upper(&n_be);
    let e_hex = u32_to_be_hex(e);

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }

        log::info!("tc_id: {}", tc.tc_id);

        result_cases.push(run_rsa_sign_case(
            timeout,
            spi_console,
            tg.modulo,
            padding,
            hashing,
            &n_le,
            &d_le,
            e,
            tc,
        )?);
    }

    Ok(RsaSignGenResultGroup {
        tg_id: tg.tg_id,
        n: n_hex,
        e: e_hex,
        tests: result_cases,
    })
}

pub fn run_rsa_siggen_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &RsaSignGenTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<RsaSignGenResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let seed = seed_arg.unwrap_or_else(rand::random::<u64>);
    log::info!("Using seed {}", seed);

    let mut drng = ChaCha8Rng::seed_from_u64(seed);
    let (skip_stride, start_offset) = match (drng.next_u32() as usize).checked_rem(skip_stride_arg)
    {
        Some(offset) => (skip_stride_arg, offset),
        None => (1usize, 0usize),
    };

    let mut result_groups = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_rsa_siggen_group(
            timeout,
            spi_console,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(RsaSignGenResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
