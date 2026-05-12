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
use cryptotest_commands::ed25519_commands::{
    CryptotestEd25519Message, CryptotestEd25519Operation, CryptotestEd25519PrivateKey,
    CryptotestEd25519PublicKey, CryptotestEd25519SignMode, CryptotestEd25519Signature,
    CryptotestEd25519VerifyOutput,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use rand::RngCore;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

// The R component of an Ed25519 signature occupies the first 32 bytes and must
// be byte-reversed when crossing the ACVP (big-endian) / device (little-endian)
// boundary.
const ED25519_SIGNATURE_R_BYTES: usize = 32;

// Test vector input structs

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EddsaTestCase {
    tc_id: usize,
    #[serde(default)]
    message: Option<String>,
    #[serde(default)]
    q: Option<String>,
    #[serde(default)]
    signature: Option<String>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct EddsaTestGroup {
    tg_id: usize,
    test_type: String,
    curve: String,
    pre_hash: bool,
    tests: Vec<EddsaTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EddsaTestVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<EddsaTestGroup>,
}

// Result structs

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EddsaResultCase {
    pub tc_id: usize,
    pub test_passed: bool,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EddsaResultGroup {
    pub tg_id: usize,
    pub tests: Vec<EddsaResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EddsaResultVectorSet {
    pub vs_id: usize,
    pub algorithm: String,
    pub mode: String,
    pub revision: String,
    #[serde(default)]
    pub is_sample: bool,
    pub test_groups: Vec<EddsaResultGroup>,
}

fn run_eddsa_verify_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tc: &EddsaTestCase,
) -> Result<EddsaResultCase> {
    let msg = Vec::<u8>::from_hex(tc.message.as_ref().unwrap())?;
    let q = Vec::<u8>::from_hex(tc.q.as_ref().unwrap())?;

    // ACVP encodes the signature in big-endian hex. The device expects the R
    // component (first 32 bytes) in little-endian byte order.
    let mut sig = Vec::<u8>::from_hex(tc.signature.as_ref().unwrap())?;
    if sig.len() >= ED25519_SIGNATURE_R_BYTES {
        sig[..ED25519_SIGNATURE_R_BYTES].reverse();
    }

    CryptotestCommand::Ed25519.send(spi_console)?;
    CryptotestEd25519Operation::Verify.send(spi_console)?;
    CryptotestEd25519SignMode::Eddsa.send(spi_console)?;

    CryptotestEd25519Message {
        input: ArrayVec::try_from(msg.as_slice())
            .map_err(|_| std::io::Error::other("Ed25519 message too large"))?,
        input_len: msg.len(),
    }
    .send(spi_console)?;

    CryptotestEd25519Signature {
        signature: ArrayVec::try_from(sig.as_slice())
            .map_err(|_| std::io::Error::other("Ed25519 signature unexpected length"))?,
        signature_len: sig.len(),
    }
    .send(spi_console)?;

    CryptotestEd25519PublicKey {
        public_key: ArrayVec::try_from(q.as_slice())
            .map_err(|_| std::io::Error::other("Ed25519 public key unexpected length"))?,
        public_key_len: q.len(),
    }
    .send(spi_console)?;

    // Private key is unused for verify; send empty shares.
    CryptotestEd25519PrivateKey {
        d0: ArrayVec::new(),
        d0_len: 0,
        d1: ArrayVec::new(),
        d1_len: 0,
    }
    .send(spi_console)?;

    let output = CryptotestEd25519VerifyOutput::recv(spi_console, timeout, false, false)?;
    let test_passed = match output {
        CryptotestEd25519VerifyOutput::Success => true,
        CryptotestEd25519VerifyOutput::Failure => false,
        CryptotestEd25519VerifyOutput::IntValue(v) => {
            return Err(std::io::Error::other(format!(
                "Unexpected Ed25519 verify output value: {}",
                v
            ))
            .into());
        }
    };

    Ok(EddsaResultCase {
        tc_id: tc.tc_id,
        test_passed,
    })
}

fn run_eddsa_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    mode: &str,
    tg: &EddsaTestGroup,
    skip_stride: usize,
    start_offset: usize,
) -> Result<EddsaResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    if tg.pre_hash {
        return Err(std::io::Error::other(format!(
            "Pre-hash mode is not yet supported (tg_id {})",
            tg.tg_id
        ))
        .into());
    }

    let stride = min(skip_stride, tg.tests.len());
    let offset = if stride > 0 { start_offset % stride } else { 0 };
    log::info!("Tests options: skip_stride: {}, offset: {}", stride, offset);

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        if stride > 0 && (tc.tc_id % stride) != offset {
            continue;
        }
        log::info!("tc_id: {}", tc.tc_id);

        if mode.eq_ignore_ascii_case("sigVer") {
            result_cases.push(run_eddsa_verify_case(timeout, spi_console, tc)?);
        } else {
            return Err(std::io::Error::other(format!(
                "EDDSA mode '{}' not implemented in harness",
                mode
            ))
            .into());
        }
    }

    Ok(EddsaResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_eddsa_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &EddsaTestVectorSet,
    skip_stride_arg: usize,
    seed_arg: Option<u64>,
) -> Result<EddsaResultVectorSet> {
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
        result_groups.push(run_eddsa_group(
            timeout,
            spi_console,
            &vs.mode,
            tg,
            skip_stride,
            start_offset,
        )?);
    }

    Ok(EddsaResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        mode: vs.mode.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
