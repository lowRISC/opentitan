// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{anyhow, Result};
use base64ct::{Base64, Decoder};
use clap::Parser;
use num_bigint_dig::BigUint;
use regex::Regex;
use std::time::Duration;

use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::sha256;
use opentitanlib::image::image::Image;
use opentitanlib::ownership::OwnerBlock;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::util::file::FromReader;

use ot_certs::template::{CertificateExtension, Value};
use ot_certs::x509;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,
}

// A helper trait for extracting data out of the `Value` type.
trait GetValue<T> {
    fn get_value(&self) -> &T;
}

impl<T: std::fmt::Debug> GetValue<T> for Value<T> {
    fn get_value(&self) -> &T {
        match self {
            Value::Variable(_) => panic!("Not expecting a Variable: {self:?}"),
            Value::Literal(x) => x,
        }
    }
}

impl<T: std::fmt::Debug> GetValue<T> for Option<Value<T>> {
    fn get_value(&self) -> &T {
        match self {
            None => panic!("Not expecting Option::None"),
            Some(Value::Variable(_)) => panic!("Not expecting a Variable: {self:?}"),
            Some(Value::Literal(x)) => x,
        }
    }
}

fn get_base64_blob(haystack: &str, rx: &str) -> Result<Vec<u8>> {
    let rx = Regex::new(rx)?;
    let encoded = rx
        .captures(haystack)
        .ok_or(anyhow!("Encoded certificate not found"))?;
    let mut bin = Vec::new();
    if !encoded[1].is_empty() {
        let mut decoder = Decoder::<Base64>::new(encoded[1].as_bytes())?;
        decoder.decode_to_end(&mut bin)?;
    }
    Ok(bin)
}

fn attestation_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport.uart("console")?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR)Running.*PASS!$|FAIL!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;

    let _uds_bin = get_base64_blob(&capture[0], r"(?msR)UDS: (.*?)$")?;
    let cdi0_bin = get_base64_blob(&capture[0], r"(?msR)CDI_0: (.*?)$")?;
    let cdi1_bin = get_base64_blob(&capture[0], r"(?msR)CDI_1: (.*?)$")?;
    let owner_page_0 = get_base64_blob(&capture[0], r"(?msR)OWNER_PAGE_0: (.*?)$")?;
    let owner_page_1 = get_base64_blob(&capture[0], r"(?msR)OWNER_PAGE_1: (.*?)$")?;

    // TODO: check UDS certificate.
    let cdi0 = x509::parse_certificate(&cdi0_bin)?;
    let cdi1 = x509::parse_certificate(&cdi1_bin)?;

    // TODO: verify signature chain from CDI_1 to CDI_0 to UDS.

    let image = Image::read_from_file(opts.init.bootstrap.bootstrap.as_deref().unwrap())?;

    // TODO: determine the correct endianness for expressing these measurements.
    let measurements = image
        .subimages()?
        .iter()
        .map(|s| s.compute_digest().unwrap().to_le_bytes())
        .collect::<Vec<_>>();
    let owner_measurements = [
        // The owner page digests should not include the signature or seal fields.
        sha256::sha256(&owner_page_0[0..OwnerBlock::SIGNATURE_OFFSET]).to_le_bytes(),
        sha256::sha256(&owner_page_1[0..OwnerBlock::SIGNATURE_OFFSET]).to_le_bytes(),
    ];

    let CertificateExtension::DiceTcbInfo(dice) = &cdi0.private_extensions[0];
    log::info!("Checking CDI_0 (ROM_EXT) DICE Extension: {dice:#?}");
    assert_eq!(dice.model.get_value(), "ROM_EXT");
    assert_eq!(dice.vendor.get_value(), "OpenTitan");
    assert_eq!(dice.layer.get_value(), &BigUint::from(1u8));
    let fw_ids = dice.fw_ids.as_ref().expect("list of fw_ids");
    assert_eq!(fw_ids.len(), 1);
    assert_eq!(fw_ids[0].digest.get_value(), &measurements[0]);

    let CertificateExtension::DiceTcbInfo(dice) = &cdi1.private_extensions[0];
    log::info!("Checking CDI_1 (Owner) DICE Extension: {dice:#?}");
    assert_eq!(dice.model.get_value(), "Owner");
    assert_eq!(dice.vendor.get_value(), "OpenTitan");
    assert_eq!(dice.layer.get_value(), &BigUint::from(2u8));
    let fw_ids = dice.fw_ids.as_ref().expect("list of fw_ids");
    assert_eq!(fw_ids.len(), 2);
    assert_eq!(fw_ids[0].digest.get_value(), &measurements[1]);
    assert_eq!(fw_ids[1].digest.get_value(), &owner_measurements[0]);
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    attestation_test(&opts, &transport)?;
    Ok(())
}
