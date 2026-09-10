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
use cryptotest_commands::ecdsa_commands::{
    CryptotestEcdsaCoordinate, CryptotestEcdsaCurve, CryptotestEcdsaHashAlg,
    CryptotestEcdsaHashDigest, CryptotestEcdsaKeygenResp, CryptotestEcdsaMessage,
    CryptotestEcdsaOperation, CryptotestEcdsaPrivateKey, CryptotestEcdsaSignature,
    CryptotestEcdsaVerifyOutput,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaTestCase {
    tc_id: usize,
    message: String,
    qx: String,
    qy: String,
    r: String,
    s: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaTestGroup {
    tg_id: usize,
    test_type: String,
    curve: String,
    hash_alg: String,
    tests: Vec<EcdsaTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaTestVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<EcdsaTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaResultCase {
    pub tc_id: usize,
    pub test_passed: bool,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaResultGroup {
    pub tg_id: usize,
    pub tests: Vec<EcdsaResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<EcdsaResultGroup>,
}

fn map_hash_alg(hash_alg: &str) -> Result<CryptotestEcdsaHashAlg> {
    match hash_alg {
        "SHA2-256" => Ok(CryptotestEcdsaHashAlg::Sha256),
        "SHA2-384" => Ok(CryptotestEcdsaHashAlg::Sha384),
        "SHA2-512" => Ok(CryptotestEcdsaHashAlg::Sha512),
        "SHA3-256" => Ok(CryptotestEcdsaHashAlg::Sha3_256),
        "SHA3-384" => Ok(CryptotestEcdsaHashAlg::Sha3_384),
        "SHA3-512" => Ok(CryptotestEcdsaHashAlg::Sha3_512),
        _ => Err(
            std::io::Error::other(format!("Unsupported ECDSA hash algorithm: {}", hash_alg)).into(),
        ),
    }
}

fn map_curve(curve: &str) -> Result<CryptotestEcdsaCurve> {
    match curve {
        "P-256" => Ok(CryptotestEcdsaCurve::P256),
        "P-384" => Ok(CryptotestEcdsaCurve::P384),
        _ => Err(std::io::Error::other(format!("Unsupported ECDSA curve: {}", curve)).into()),
    }
}

fn run_ecdsa_verify_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    hash_alg: &str,
    curve: &str,
    tc: &EcdsaTestCase,
) -> Result<EcdsaResultCase> {
    let msg = Vec::<u8>::from_hex(&tc.message)?;

    // Step 1: hash the raw message on device.
    CryptotestCommand::Ecdsa.send(spi_console)?;
    CryptotestEcdsaOperation::Hash.send(spi_console)?;
    map_hash_alg(hash_alg)?.send(spi_console)?;
    CryptotestEcdsaMessage {
        input: ArrayVec::try_from(msg.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA message too large"))?,
        input_len: msg.len(),
    }
    .send(spi_console)?;

    let hash_resp = CryptotestEcdsaHashDigest::recv(spi_console, timeout, false, false)?;
    let digest = &hash_resp.digest.as_slice()[..hash_resp.digest_len];

    // Step 2: verify the signature against the digest.
    // ACVP vectors encode qx, qy, r, s as big-endian zero-padded hex;
    // the device expects little-endian byte arrays.
    let mut qx = Vec::<u8>::from_hex(&tc.qx)?;
    qx.reverse();
    let mut qy = Vec::<u8>::from_hex(&tc.qy)?;
    qy.reverse();
    let mut r = Vec::<u8>::from_hex(&tc.r)?;
    r.reverse();
    let mut s = Vec::<u8>::from_hex(&tc.s)?;
    s.reverse();

    CryptotestCommand::Ecdsa.send(spi_console)?;
    CryptotestEcdsaOperation::Verify.send(spi_console)?;
    map_hash_alg(hash_alg)?.send(spi_console)?;
    map_curve(curve)?.send(spi_console)?;

    CryptotestEcdsaMessage {
        input: ArrayVec::try_from(digest)
            .map_err(|_| std::io::Error::other("ECDSA digest too large for message buffer"))?,
        input_len: digest.len(),
    }
    .send(spi_console)?;

    CryptotestEcdsaSignature {
        r: ArrayVec::try_from(r.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA r value too large"))?,
        r_len: r.len(),
        s: ArrayVec::try_from(s.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA s value too large"))?,
        s_len: s.len(),
    }
    .send(spi_console)?;

    CryptotestEcdsaCoordinate {
        coordinate: ArrayVec::try_from(qx.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA qx too large"))?,
        coordinate_len: qx.len(),
    }
    .send(spi_console)?;

    CryptotestEcdsaCoordinate {
        coordinate: ArrayVec::try_from(qy.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA qy too large"))?,
        coordinate_len: qy.len(),
    }
    .send(spi_console)?;

    // Private key is unused for verify; send empty shares.
    CryptotestEcdsaPrivateKey {
        d0: ArrayVec::new(),
        d0_len: 0,
        d1: ArrayVec::new(),
        d1_len: 0,
        unmasked_len: 0,
    }
    .send(spi_console)?;

    let output = CryptotestEcdsaVerifyOutput::recv(spi_console, timeout, false, false)?;
    let test_passed = match output {
        CryptotestEcdsaVerifyOutput::Success => true,
        CryptotestEcdsaVerifyOutput::Failure => false,
        CryptotestEcdsaVerifyOutput::IntValue(v) => {
            return Err(std::io::Error::other(format!(
                "Unexpected ECDSA verify output value: {}",
                v
            ))
            .into());
        }
    };

    Ok(EcdsaResultCase {
        tc_id: tc.tc_id,
        test_passed,
    })
}

fn run_ecdsa_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &EcdsaTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<EcdsaResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    // Validate algorithm and curve up front so we fail fast on unsupported configs.
    map_hash_alg(&tg.hash_alg)?;
    map_curve(&tg.curve)?;

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Test options: skip_stride: {}, offset: {}", stride, offset);

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        log::info!("tc_id: {}", tc.tc_id);
        result_cases.push(run_ecdsa_verify_case(
            timeout,
            spi_console,
            &tg.hash_alg,
            &tg.curve,
            tc,
        )?);
    }

    Ok(EcdsaResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_ecdsa_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &EcdsaTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<EcdsaResultVectorSet> {
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
        result_groups.push(run_ecdsa_group(
            timeout,
            spi_console,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(EcdsaResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        mode: vs.mode.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}

// sigGen

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaSignGenTestCase {
    tc_id: usize,
    message: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaSignGenTestGroup {
    tg_id: usize,
    test_type: String,
    curve: String,
    hash_alg: String,
    #[serde(default)]
    component_test: bool,
    tests: Vec<EcdsaSignGenTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaSignGenTestVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<EcdsaSignGenTestGroup>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaSignGenResultCase {
    pub tc_id: usize,
    pub r: String,
    pub s: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaSignGenResultGroup {
    pub tg_id: usize,
    pub qx: String,
    pub qy: String,
    pub tests: Vec<EcdsaSignGenResultCase>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaSignGenResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<EcdsaSignGenResultGroup>,
}

fn curve_scalar_bytes(curve: &str) -> Result<usize> {
    match curve {
        "P-256" => Ok(32),
        "P-384" => Ok(48),
        _ => Err(std::io::Error::other(format!("Unsupported curve: {}", curve)).into()),
    }
}

// (qx_le, qy_le, d0_le, d1_le, d_le) from a KeyGen response.
type KeygenRaw = (Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>);

// Sends KeyGen, receives qx/qy/d0/d1/d as little-endian byte vecs.
fn run_ecdsa_keygen(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    curve: &str,
) -> Result<KeygenRaw> {
    CryptotestCommand::Ecdsa.send(spi_console)?;
    CryptotestEcdsaOperation::KeyGen.send(spi_console)?;
    map_curve(curve)?.send(spi_console)?;

    let resp = CryptotestEcdsaKeygenResp::recv(spi_console, timeout, false, false)?;
    let qx = resp.qx.as_slice()[..resp.qx_len].to_vec();
    let qy = resp.qy.as_slice()[..resp.qy_len].to_vec();
    let d0 = resp.d0.as_slice()[..resp.d0_len].to_vec();
    let d1 = resp.d1.as_slice()[..resp.d1_len].to_vec();
    let d = resp.d.as_slice()[..resp.d_len].to_vec();
    Ok((qx, qy, d0, d1, d))
}

// Runs Hash then Sign for one sigGen test case. Returns (r_be_hex, s_be_hex).
#[allow(clippy::too_many_arguments)]
fn run_ecdsa_sign_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    hash_alg: &str,
    curve: &str,
    qx_le: &[u8],
    qy_le: &[u8],
    d0_le: &[u8],
    d1_le: &[u8],
    tc: &EcdsaSignGenTestCase,
) -> Result<EcdsaSignGenResultCase> {
    let msg = Vec::<u8>::from_hex(&tc.message)?;

    // Step 1: hash the message on device.
    CryptotestCommand::Ecdsa.send(spi_console)?;
    CryptotestEcdsaOperation::Hash.send(spi_console)?;
    map_hash_alg(hash_alg)?.send(spi_console)?;
    CryptotestEcdsaMessage {
        input: arrayvec::ArrayVec::try_from(msg.as_slice())
            .map_err(|_| std::io::Error::other("ECDSA message too large"))?,
        input_len: msg.len(),
    }
    .send(spi_console)?;

    let hash_resp = CryptotestEcdsaHashDigest::recv(spi_console, timeout, false, false)?;
    let digest = &hash_resp.digest.as_slice()[..hash_resp.digest_len];

    // Step 2: sign the digest with the key from keygen.
    CryptotestCommand::Ecdsa.send(spi_console)?;
    CryptotestEcdsaOperation::Sign.send(spi_console)?;
    map_hash_alg(hash_alg)?.send(spi_console)?;
    map_curve(curve)?.send(spi_console)?;

    CryptotestEcdsaMessage {
        input: arrayvec::ArrayVec::try_from(digest)
            .map_err(|_| std::io::Error::other("ECDSA digest too large for message buffer"))?,
        input_len: digest.len(),
    }
    .send(spi_console)?;

    // Signature buffer is output-only; send empty.
    CryptotestEcdsaSignature {
        r: arrayvec::ArrayVec::new(),
        r_len: 0,
        s: arrayvec::ArrayVec::new(),
        s_len: 0,
    }
    .send(spi_console)?;

    CryptotestEcdsaCoordinate {
        coordinate: arrayvec::ArrayVec::try_from(qx_le)
            .map_err(|_| std::io::Error::other("ECDSA qx too large"))?,
        coordinate_len: qx_le.len(),
    }
    .send(spi_console)?;

    CryptotestEcdsaCoordinate {
        coordinate: arrayvec::ArrayVec::try_from(qy_le)
            .map_err(|_| std::io::Error::other("ECDSA qy too large"))?,
        coordinate_len: qy_le.len(),
    }
    .send(spi_console)?;

    let unmasked_len = curve_scalar_bytes(curve)?;
    CryptotestEcdsaPrivateKey {
        d0: arrayvec::ArrayVec::try_from(d0_le)
            .map_err(|_| std::io::Error::other("ECDSA d0 too large"))?,
        d0_len: d0_le.len(),
        d1: arrayvec::ArrayVec::try_from(d1_le)
            .map_err(|_| std::io::Error::other("ECDSA d1 too large"))?,
        d1_len: d1_le.len(),
        unmasked_len,
    }
    .send(spi_console)?;

    let sig = CryptotestEcdsaSignature::recv(spi_console, timeout, false, false)?;
    let mut r = sig.r.as_slice()[..sig.r_len].to_vec();
    let mut s = sig.s.as_slice()[..sig.s_len].to_vec();
    r.reverse();
    s.reverse();

    Ok(EcdsaSignGenResultCase {
        tc_id: tc.tc_id,
        r: hex::encode_upper(&r),
        s: hex::encode_upper(&s),
    })
}

fn run_ecdsa_siggen_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &EcdsaSignGenTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<EcdsaSignGenResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    map_hash_alg(&tg.hash_alg)?;
    map_curve(&tg.curve)?;

    // One key per group; all test cases share it.
    let (qx_le, qy_le, d0_le, d1_le, _d_le) = run_ecdsa_keygen(timeout, spi_console, &tg.curve)?;

    let mut qx_be = qx_le.clone();
    qx_be.reverse();
    let mut qy_be = qy_le.clone();
    qy_be.reverse();
    let qx_hex = hex::encode_upper(&qx_be);
    let qy_hex = hex::encode_upper(&qy_be);

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Test options: skip_stride: {}, offset: {}", stride, offset);

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        log::info!("tc_id: {}", tc.tc_id);
        result_cases.push(run_ecdsa_sign_case(
            timeout,
            spi_console,
            &tg.hash_alg,
            &tg.curve,
            &qx_le,
            &qy_le,
            &d0_le,
            &d1_le,
            tc,
        )?);
    }

    Ok(EcdsaSignGenResultGroup {
        tg_id: tg.tg_id,
        qx: qx_hex,
        qy: qy_hex,
        tests: result_cases,
    })
}

pub fn run_ecdsa_siggen_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &EcdsaSignGenTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<EcdsaSignGenResultVectorSet> {
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
        result_groups.push(run_ecdsa_siggen_group(
            timeout,
            spi_console,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(EcdsaSignGenResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        mode: vs.mode.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}

// keyGen

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaKeyGenTestCase {
    tc_id: usize,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EcdsaKeyGenTestGroup {
    tg_id: usize,
    test_type: String,
    curve: String,
    secret_generation_mode: String,
    tests: Vec<EcdsaKeyGenTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaKeyGenTestVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<EcdsaKeyGenTestGroup>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaKeyGenResultCase {
    pub tc_id: usize,
    pub d: String,
    pub qx: String,
    pub qy: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaKeyGenResultGroup {
    pub tg_id: usize,
    pub tests: Vec<EcdsaKeyGenResultCase>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EcdsaKeyGenResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<EcdsaKeyGenResultGroup>,
}

fn run_ecdsa_keygen_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    curve: &str,
    tc: &EcdsaKeyGenTestCase,
) -> Result<EcdsaKeyGenResultCase> {
    let (qx_le, qy_le, _d0_le, _d1_le, d_le) = run_ecdsa_keygen(timeout, spi_console, curve)?;

    let mut qx_be = qx_le;
    qx_be.reverse();
    let mut qy_be = qy_le;
    qy_be.reverse();
    let mut d_be = d_le;
    d_be.reverse();

    Ok(EcdsaKeyGenResultCase {
        tc_id: tc.tc_id,
        d: hex::encode_upper(&d_be),
        qx: hex::encode_upper(&qx_be),
        qy: hex::encode_upper(&qy_be),
    })
}

fn run_ecdsa_keygen_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &EcdsaKeyGenTestGroup,
) -> Result<EcdsaKeyGenResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    map_curve(&tg.curve)?;

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        log::info!("tc_id: {}", tc.tc_id);
        result_cases.push(run_ecdsa_keygen_case(timeout, spi_console, &tg.curve, tc)?);
    }

    Ok(EcdsaKeyGenResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_ecdsa_keygen_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &EcdsaKeyGenTestVectorSet,
) -> Result<EcdsaKeyGenResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let mut result_groups = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_ecdsa_keygen_group(timeout, spi_console, tg)?);
    }

    Ok(EcdsaKeyGenResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        mode: vs.mode.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
