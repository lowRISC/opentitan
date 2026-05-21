// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::x25519_commands::{
    CryptotestX25519KexOutput, CryptotestX25519PublicKey, X25519Subcommand,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};

// Input structs (from x25519_vectors.hjson)

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct X25519TestCase {
    tc_id: usize,
    public_server: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct X25519TestGroup {
    tg_id: usize,
    #[allow(dead_code)]
    test_type: String,
    #[allow(dead_code)]
    curve: String,
    tests: Vec<X25519TestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct X25519TestVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<X25519TestGroup>,
}

// Output structs (for the JSON result file)

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct X25519ResultCase {
    tc_id: usize,
    public_iut: String,
    z: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct X25519ResultGroup {
    tg_id: usize,
    tests: Vec<X25519ResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct X25519ResultVectorSet {
    vs_id: usize,
    algorithm: String,
    mode: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<X25519ResultGroup>,
}

fn run_x25519_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tc: &X25519TestCase,
) -> Result<X25519ResultCase> {
    let public_server = Vec::<u8>::from_hex(&tc.public_server)?;

    CryptotestCommand::X25519.send(spi_console)?;
    X25519Subcommand::X25519KEX.send(spi_console)?;

    CryptotestX25519PublicKey {
        public_key: ArrayVec::try_from(public_server.as_slice())
            .map_err(|_| std::io::Error::other("X25519 server public key unexpected length"))?,
        public_key_len: public_server.len(),
    }
    .send(spi_console)?;

    let output = CryptotestX25519KexOutput::recv(spi_console, timeout, false, false)?;

    let public_iut = &output.public_key[..output.public_key_len];
    let z = &output.shared_secret[..output.shared_secret_len];

    Ok(X25519ResultCase {
        tc_id: tc.tc_id,
        public_iut: hex::encode_upper(public_iut),
        z: hex::encode_upper(z),
    })
}

fn run_x25519_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    tg: &X25519TestGroup,
) -> Result<X25519ResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);

    let mut result_cases = Vec::new();
    for tc in &tg.tests {
        log::info!("tc_id: {}", tc.tc_id);
        result_cases.push(run_x25519_case(timeout, spi_console, tc)?);
    }

    Ok(X25519ResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_x25519_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &X25519TestVectorSet,
) -> Result<X25519ResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);

    let mut result_groups = Vec::with_capacity(vs.test_groups.len());
    for tg in &vs.test_groups {
        result_groups.push(run_x25519_group(timeout, spi_console, tg)?);
    }

    Ok(X25519ResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        mode: vs.mode.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
