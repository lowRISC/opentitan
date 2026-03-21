// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use hex::FromHex;
use serde::{Deserialize, Serialize};
use std::time::Duration;

use cryptotest_commands::commands::CryptotestCommand;
use cryptotest_commands::hash_commands::{
    CryptotestHashAlgorithm, CryptotestHashMessage, CryptotestHashOutput,
    CryptotestHashShakeDigestLength,
};

use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CshakeTestCase {
    tc_id: usize,
    msg: String,
    #[serde(default)]
    customization: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CshakeTestGroup {
    tg_id: usize,
    test_type: String,
    msg_len: usize,
    mac_len: usize,
    tests: Vec<CshakeTestCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CshakeTestVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<CshakeTestGroup>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CshakeResultCase {
    tc_id: usize,
    mac: String,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
struct CshakeResultGroup {
    tg_id: usize,
    tests: Vec<CshakeResultCase>,
}

#[derive(Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CshakeResultVectorSet {
    vs_id: usize,
    algorithm: String,
    revision: String,
    #[serde(default)]
    is_sample: bool,
    test_groups: Vec<CshakeResultGroup>,
}

fn run_cshake_case(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &CryptotestHashAlgorithm,
    mac_len: usize,
    tc: &CshakeTestCase,
) -> Result<CshakeResultCase> {
    log::info!("tc_id: {}", tc.tc_id);
    let msg = Vec::<u8>::from_hex(tc.msg.as_bytes())?;
    let cust_str = Vec::<u8>::from_hex(tc.customization.as_bytes()).unwrap_or_default();

    CryptotestCommand::Hash.send(spi_console)?;

    algorithm.send(spi_console)?;

    CryptotestHashShakeDigestLength {
        length: mac_len / 8,
    }
    .send(spi_console)?;

    CryptotestHashMessage {
        message: arrayvec::ArrayVec::try_from(msg.as_slice()).unwrap(),
        message_len: msg.len(),
        customization_string: arrayvec::ArrayVec::try_from(cust_str.as_slice()).unwrap(),
        customization_string_len: cust_str.len(),
    }
    .send(spi_console)?;

    let hash_output = CryptotestHashOutput::recv(spi_console, timeout, false, false)?;

    let returned_bits = hash_output.oneshot_digest
        [..std::cmp::min(mac_len / 8, hash_output.digest_len)]
        .iter()
        .try_fold(String::new(), |mut acc, w| {
            core::fmt::write(&mut acc, core::format_args!("{:02x}", w))
                .or(Err(std::io::Error::from(std::io::ErrorKind::Other)))?;
            Ok::<String, std::io::Error>(acc)
        })?;

    Ok(CshakeResultCase {
        tc_id: tc.tc_id,
        mac: returned_bits,
    })
}

fn run_cshake_group(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    algorithm: &CryptotestHashAlgorithm,
    tg: &CshakeTestGroup,
) -> Result<CshakeResultGroup> {
    log::info!("tg_id: {}", tg.tg_id);
    let mut result_cases: Vec<CshakeResultCase> = Vec::with_capacity(tg.tests.len());
    for tc in &tg.tests {
        result_cases.push(run_cshake_case(
            timeout,
            spi_console,
            algorithm,
            tg.mac_len,
            tc,
        )?);
    }
    Ok(CshakeResultGroup {
        tg_id: tg.tg_id,
        tests: result_cases,
    })
}

pub fn run_cshake_vector_set(
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    vs: &CshakeTestVectorSet,
) -> Result<CshakeResultVectorSet> {
    log::info!("vs_id: {}", vs.vs_id);
    let mut result_groups: Vec<CshakeResultGroup> = Vec::with_capacity(vs.test_groups.len());

    let algorithm = match vs.algorithm.as_str() {
        "cSHAKE-128" => CryptotestHashAlgorithm::Cshake128,
        "cSHAKE-256" => CryptotestHashAlgorithm::Cshake256,
        _ => return Err(std::io::Error::from(std::io::ErrorKind::InvalidInput).into()),
    };

    for tg in &vs.test_groups {
        result_groups.push(run_cshake_group(timeout, spi_console, &algorithm, tg)?);
    }
    Ok(CshakeResultVectorSet {
        vs_id: vs.vs_id,
        algorithm: vs.algorithm.clone(),
        revision: vs.revision.clone(),
        is_sample: vs.is_sample,
        test_groups: result_groups,
    })
}
