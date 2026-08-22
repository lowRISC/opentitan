// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::bool_assert_comparison)]
use anyhow::{Result, anyhow, bail};
use base64ct::{Base64, Decoder};
use clap::Parser;
use core::option::Option;
use num_bigint_dig::BigUint;
use regex::Regex;
use std::time::Duration;
use tempfile::TempDir;

use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::image::image::Image;
use opentitanlib::ownership::OwnerBlock;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;
use opentitanlib::util::file::FromReader;

use ot_certs::template::{
    AttributeType, Certificate, CertificateExtension, Name, Selectable, SubjectPublicKeyInfo, Value,
};
use ot_certs::x509;
use runfiles::{Runfiles, rlocation};

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Console receive timeout.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "10s")]
    timeout: Duration,

    /// Enable verification of ML-DSA certificates
    #[arg(long)]
    test_mldsa: bool,

    /// Enable verification of attestation chains after provisioning. This allows testing chains
    /// starting from UDS certificates stored during provisioning
    #[arg(long)]
    post_provisioning_tests: bool,

    /// Assert that ML-DSA certificates are handed over from Flash storage.
    #[arg(long)]
    assert_mldsa_flash_storage: bool,

    /// Assert that ML-DSA flash region is reported as occupied warning.
    #[arg(long)]
    assert_mldsa_overlapped: bool,
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

fn find_openssl_bin() -> Result<std::path::PathBuf> {
    let r = Runfiles::create()?;
    if let Some(path) = rlocation!(r, "openssl/openssl") {
        if path.exists() {
            return Ok(path);
        }
    }
    anyhow::bail!("Could not find @openssl//:openssl binary in runfiles");
}

fn get_base64_str(haystack: &str, rx: &str) -> Result<String> {
    let rx = Regex::new(rx)?;
    let captured = rx
        .captures(haystack)
        .ok_or(anyhow!("Base64 blob not found"))?;
    Ok(captured[1].trim().to_string())
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

fn check_public_key(
    key: &Selectable<SubjectPublicKeyInfo>,
    id: &[u8],
    subject: &Name,
) -> Result<bool> {
    let key = match key {
        Selectable::Value(val) => val,
        Selectable::Choice(_) => {
            unreachable!("Selector cannot appear in parsed DER certificates")
        }
    };
    let material = match key {
        SubjectPublicKeyInfo::EcPublicKey(info) => {
            let mut material = Vec::new();
            let x = &info.public_key.x.get_value().to_bytes_be();
            let y = &info.public_key.y.get_value().to_bytes_be();
            material.extend(vec![0; 32 - x.len()]);
            material.extend(x);
            material.extend(vec![0; 32 - y.len()]);
            material.extend(y);
            material
        }
        SubjectPublicKeyInfo::Mldsa44(info)
        | SubjectPublicKeyInfo::Mldsa65(info)
        | SubjectPublicKeyInfo::Mldsa87(info) => info.public_key.get_value().clone(),
    };

    let hash = Sha256Digest::hash(&material).to_vec();
    let keyid = &hash[..20];
    log::info!("computed id = {:?}", hex::encode(keyid));
    log::info!("         id = {:?}", hex::encode(id));

    let name = subject[0][&AttributeType::SerialNumber].get_value();
    log::info!("    subject = {:?}", name);

    Ok(keyid == id && &hex::encode(keyid) == name)
}

fn attestation_test(opts: &Opts, transport: &TransportWrapper, owner_history: &[u8]) -> Result<()> {
    let uart = transport.uart("console")?;
    let capture = UartConsole::wait_for(
        &*uart,
        r"(?msR).*PASS!$|FAIL!$|BFV:([0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;

    // Note: Finding UDS is allowed to fail on FPGA environments.
    let uds_bin = if opts.post_provisioning_tests {
        Some(get_base64_blob(&capture[0], r"(?msR)UDS: (.*?)$")?)
    } else {
        None
    };
    let cdi0_bin = get_base64_blob(&capture[0], r"(?msR)CDI_0: (.*?)$")?;
    let cdi1_bin = get_base64_blob(&capture[0], r"(?msR)CDI_1: (.*?)$")?;
    let owner_page_0 = get_base64_blob(&capture[0], r"(?msR)OWNER_PAGE_0: (.*?)$")?;
    let owner_page_1 = get_base64_blob(&capture[0], r"(?msR)OWNER_PAGE_1: (.*?)$")?;

    let uds = uds_bin
        .as_ref()
        .map(|b| x509::parse_certificate(b))
        .transpose()?;
    let cdi0 = x509::parse_certificate(&cdi0_bin)?;
    let cdi1 = x509::parse_certificate(&cdi1_bin)?;

    let uds_b64 = uds_bin
        .map(|_| get_base64_str(&capture[0], r"(?msR)UDS: (.*?)$"))
        .transpose()?;
    let cdi0_b64 = get_base64_str(&capture[0], r"(?msR)CDI_0: (.*?)$")?;
    let cdi1_b64 = get_base64_str(&capture[0], r"(?msR)CDI_1: (.*?)$")?;

    log::info!("Verifying EC-DSA chain with OpenSSL...");
    if let Some(uds_b64) = uds_b64 {
        verify_cert_partial_chain(&[&uds_b64, &cdi0_b64, &cdi1_b64])?;
    } else {
        verify_cert_partial_chain(&[&cdi0_b64, &cdi1_b64])?;
    }
    log::info!("OpenSSL EC-DSA verification successful!");

    if opts.test_mldsa {
        verify_mldsa_certs(&capture[0], uds.as_ref(), &cdi0, &cdi1)?;
        check_mldsa_storage_mode(&capture[0], opts.assert_mldsa_flash_storage)?;
        check_mldsa_flash_overlapped(&capture[0], opts.assert_mldsa_overlapped)?;
    }

    let image = Image::read_from_file(opts.init.bootstrap.bootstrap.as_deref().unwrap())?;

    let measurements = image
        .subimages()?
        .iter()
        .map(|s| s.compute_digest().unwrap())
        .collect::<Vec<_>>();
    let owner_measurements = [
        // The owner page digests should not include the signature or seal fields.
        Sha256Digest::hash(&owner_page_0[0..OwnerBlock::SIGNATURE_OFFSET]).to_vec(),
        Sha256Digest::hash(&owner_page_1[0..OwnerBlock::SIGNATURE_OFFSET]).to_vec(),
    ];

    let CertificateExtension::DiceTcbInfo(dice) = &cdi0.private_extensions[0];
    log::info!("Checking CDI_0 (ROM_EXT) DICE certificate: {cdi0:#?}");
    // Check that the subject key and subject key identifiers match.
    log::info!("Subject key:");
    assert!(check_public_key(
        &cdi0.subject_public_key_info,
        cdi0.subject_key_identifier.get_value(),
        &cdi0.subject,
    )?);
    assert_eq!(dice.model.get_value(), "ROM_EXT");
    assert_eq!(dice.vendor.get_value(), "OpenTitan");
    assert_eq!(dice.layer.get_value(), &BigUint::from(1u8));
    let fw_ids = dice
        .fw_ids
        .as_ref()
        .and_then(|ids| ids.as_type())
        .expect("list of fw_ids");
    assert_eq!(fw_ids.len(), 1);
    assert_eq!(fw_ids[0].digest.get_value(), &measurements[0].as_ref());

    let CertificateExtension::DiceTcbInfo(dice) = &cdi1.private_extensions[0];
    log::info!("Checking CDI_1 (Owner) DICE certificate: {cdi1:#?}");
    // Check that the subject key and subject key identifiers match.
    log::info!("Subject key:");
    assert!(check_public_key(
        &cdi1.subject_public_key_info,
        cdi1.subject_key_identifier.get_value(),
        &cdi1.subject,
    )?);
    // Check that the authority key identifier of CDI_1 is the subject key of CDI_0.
    log::info!("Issuer key:");
    assert!(check_public_key(
        &cdi0.subject_public_key_info,
        cdi1.authority_key_identifier.get_value(),
        &cdi1.issuer,
    )?);
    assert_eq!(dice.model.get_value(), "Owner");
    assert_eq!(dice.vendor.get_value(), "OpenTitan");
    assert_eq!(dice.layer.get_value(), &BigUint::from(2u8));
    let fw_ids = dice
        .fw_ids
        .as_ref()
        .and_then(|ids| ids.as_type())
        .expect("list of fw_ids");
    assert_eq!(fw_ids.len(), 3);
    assert_eq!(fw_ids[0].digest.get_value(), &measurements[1].as_ref());
    assert_eq!(fw_ids[1].digest.get_value(), &owner_measurements[0]);
    assert_eq!(fw_ids[2].digest.get_value(), &owner_history);
    Ok(())
}

fn compare_certs_except_keys(cert1: &Certificate, cert2: &Certificate) -> Result<()> {
    if cert1.not_before != cert2.not_before {
        return Err(anyhow!(
            "not_before mismatch: {:?} vs {:?}",
            cert1.not_before,
            cert2.not_before
        ));
    }
    if cert1.not_after != cert2.not_after {
        return Err(anyhow!(
            "not_after mismatch: {:?} vs {:?}",
            cert1.not_after,
            cert2.not_after
        ));
    }
    if cert1.basic_constraints != cert2.basic_constraints {
        return Err(anyhow!(
            "basic_constraints mismatch: {:?} vs {:?}",
            cert1.basic_constraints,
            cert2.basic_constraints
        ));
    }
    if cert1.key_usage != cert2.key_usage {
        return Err(anyhow!(
            "key_usage mismatch: {:?} vs {:?}",
            cert1.key_usage,
            cert2.key_usage
        ));
    }
    if cert1.private_extensions != cert2.private_extensions {
        return Err(anyhow!(
            "private_extensions mismatch: {:?} vs {:?}",
            cert1.private_extensions,
            cert2.private_extensions
        ));
    }
    Ok(())
}

fn check_mldsa_storage_mode(console_output: &str, assert_flash: bool) -> Result<()> {
    let expected_mode = if assert_flash { "Flash" } else { "RAM" };
    let rx = Regex::new(&format!(r"DICE cert storage mode: {expected_mode}"))?;
    if !rx.is_match(console_output) {
        return Err(anyhow!(
            "Expected 'DICE cert storage mode: {expected_mode}' log message not found in console output"
        ));
    }
    log::info!("DICE cert storage mode assertion passed ({expected_mode})!");
    Ok(())
}

fn check_mldsa_flash_overlapped(console_output: &str, assert_overlapped: bool) -> Result<()> {
    let rx_overlapped = Regex::new("warning: ML-DSA flash region occupied")?;
    if assert_overlapped {
        if !rx_overlapped.is_match(console_output) {
            return Err(anyhow!(
                "Expected 'warning: ML-DSA flash region occupied' log message not found in console output"
            ));
        }
        log::info!("ML-DSA flash region occupied warning assertion passed!");
    } else if rx_overlapped.is_match(console_output) {
        return Err(anyhow!(
            "Unexpected 'warning: ML-DSA flash region occupied' log message found in console output"
        ));
    }
    Ok(())
}

fn verify_cert_partial_chain(chain_certs_b64: &[&str]) -> Result<()> {
    let chain_certs_pem: Vec<String> = chain_certs_b64
        .iter()
        .map(|b64_cert| {
            format!(
                "-----BEGIN CERTIFICATE-----\n{}\n-----END CERTIFICATE-----\n",
                b64_cert
            )
        })
        .collect();

    if let [root_cert, intermediate_certs @ .., leaf_cert] = &chain_certs_pem[..] {
        let openssl_bin = find_openssl_bin()?;

        let temp_dir = TempDir::new()?;
        let ca_cert_filepath = temp_dir.path().join("ca_cert.pem");
        std::fs::write(&ca_cert_filepath, root_cert)?;

        let intermediate_certs_filepath = temp_dir.path().join("intermediate_certs.pem");
        std::fs::write(&intermediate_certs_filepath, intermediate_certs.join("\n"))?;

        let leaf_cert_filepath = temp_dir.path().join("leaf_cert.pem");
        std::fs::write(&leaf_cert_filepath, leaf_cert)?;
        let mut args: Vec<String> = vec![
            "verify",
            "-partial_chain",
            "-ignore_critical",
            "-show_chain",
            "-verbose",
            "-CAfile",
            ca_cert_filepath
                .to_str()
                .ok_or(anyhow::anyhow!("Invalid CA cert filepath"))?,
        ]
        .into_iter()
        .map(String::from)
        .collect();
        if chain_certs_pem.len() > 2 {
            args.extend(
                [
                    "-untrusted",
                    intermediate_certs_filepath
                        .to_str()
                        .ok_or(anyhow::anyhow!("Invalid intermediate certs filepath"))?,
                ]
                .map(String::from),
            );
        }
        args.push(
            leaf_cert_filepath
                .to_str()
                .map(String::from)
                .ok_or(anyhow::anyhow!("Invalid leaf cert filepath"))?,
        );

        let output = std::process::Command::new(openssl_bin)
            .args(&args)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            return Err(anyhow!(
                "OpenSSL certificate chain verification failed!\nArgs: {:?}\nStdout: {}\nStderr: {}",
                args,
                stdout,
                stderr
            ));
        } else {
            let stdout = String::from_utf8_lossy(&output.stdout);
            log::info!("Verified chain: {}", stdout);
        }
        Ok(())
    } else {
        bail!(
            "Chain length: {}.At least 2 certificates needed to verify chain!",
            chain_certs_b64.len()
        );
    }
}

/// Verify ML-DSA certificates if requested and structurally compare them to ECDSA certs.
fn verify_mldsa_certs(
    console_output: &str,
    uds_ecdsa: Option<&Certificate>,
    cdi0_ecdsa: &Certificate,
    cdi1_ecdsa: &Certificate,
) -> Result<()> {
    log::info!("ML-DSA verification requested. Performing verification...");
    let uds_mldsa_bin = uds_ecdsa
        .map(|_| get_base64_blob(console_output, r"(?msR)UDS_MLDSA_CERT: (.*?)$"))
        .transpose()?;
    let cdi0_mldsa_bin = get_base64_blob(console_output, r"(?msR)CDI_0_MLDSA: (.*?)$")?;
    let cdi1_mldsa_bin = get_base64_blob(console_output, r"(?msR)CDI_1_MLDSA: (.*?)$")?;

    let uds_mldsa = uds_mldsa_bin
        .as_ref()
        .map(|bin| x509::parse_certificate(bin))
        .transpose()?;
    let cdi0_mldsa = x509::parse_certificate(&cdi0_mldsa_bin)?;
    let cdi1_mldsa = x509::parse_certificate(&cdi1_mldsa_bin)?;

    let uds_mldsa_b64 = uds_mldsa_bin
        .map(|_| get_base64_str(console_output, r"(?msR)UDS_MLDSA_CERT: (.*?)$"))
        .transpose()?;
    let cdi0_mldsa_b64 = get_base64_str(console_output, r"(?msR)CDI_0_MLDSA: (.*?)$")?;
    let cdi1_mldsa_b64 = get_base64_str(console_output, r"(?msR)CDI_1_MLDSA: (.*?)$")?;

    log::info!("Verifying ML-DSA chain with OpenSSL...");
    if let Some(uds_mldsa_b64) = uds_mldsa_b64 {
        verify_cert_partial_chain(&[&uds_mldsa_b64, &cdi0_mldsa_b64, &cdi1_mldsa_b64])?;
    } else {
        verify_cert_partial_chain(&[&cdi0_mldsa_b64, &cdi1_mldsa_b64])?;
    }
    log::info!("OpenSSL ML-DSA verification successful!");

    log::info!("Comparing ML-DSA and ECDSA certificates for structural equivalence...");
    match (uds_ecdsa, uds_mldsa) {
        (Some(uds_ecdsa), Some(uds_mldsa)) => compare_certs_except_keys(uds_ecdsa, &uds_mldsa)?,
        (None, None) => (),
        _ => unreachable!(),
    }
    compare_certs_except_keys(cdi0_ecdsa, &cdi0_mldsa)?;
    compare_certs_except_keys(cdi1_ecdsa, &cdi1_mldsa)?;
    log::info!("Structural equivalence verification successful!");

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    // If there haven't been any ownership transfers, the owner history will be all ones.
    attestation_test(&opts, &transport, &[255u8; 32])?;
    Ok(())
}
