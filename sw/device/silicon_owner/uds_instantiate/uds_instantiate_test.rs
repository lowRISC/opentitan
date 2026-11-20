// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow, bail};
use base64ct::{Base64, Decoder};
use clap::Parser;
use num_bigint_dig::BigUint;
use regex::Regex;
use runfiles::{Runfiles, rlocation};
use tempfile::TempDir;

use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::uart::console::UartConsole;

use ot_certs::template::{
    AttributeType, CertificateExtension, Name, Selectable, SubjectPublicKeyInfo, Value,
};
use ot_certs::x509;

#[derive(Debug, Parser)]
struct Opts {
    #[command(flatten)]
    init: InitializeTest,

    /// Optional second image (assembled ML-DSA ROM_EXT + uds_instantiate) to bootstrap
    /// after running a factory UDS provisioning helper in `--bootstrap`.
    #[arg(long)]
    second_bootstrap: Option<PathBuf>,

    /// Expect a factory P-256 UDS certificate in FactoryCerts and verify verbatim
    /// dice_tcb_info extension copying plus the full 6-certificate chain.
    #[arg(long)]
    expect_factory_uds: bool,

    /// Console receive timeout per boot phase.
    #[arg(long, value_parser = humantime::parse_duration, default_value = "45s")]
    timeout: Duration,
}

trait GetValue<T> {
    fn get_value(&self) -> &T;
}

impl<T: std::fmt::Debug> GetValue<T> for Value<T> {
    fn get_value(&self) -> &T {
        match self {
            Value::Variable(_) => panic!("Unexpected template variable in parsed cert: {self:?}"),
            Value::Literal(x) => x,
        }
    }
}

impl<T: std::fmt::Debug> GetValue<T> for Option<Value<T>> {
    fn get_value(&self) -> &T {
        match self {
            None => panic!("Unexpected Option::None in parsed cert"),
            Some(Value::Variable(_)) => {
                panic!("Unexpected template variable in parsed cert: {self:?}")
            }
            Some(Value::Literal(x)) => x,
        }
    }
}

fn find_openssl_bin() -> Result<PathBuf> {
    let r = Runfiles::create()?;
    if let Some(path) = rlocation!(r, "openssl/openssl")
        && path.exists()
    {
        return Ok(path);
    }
    bail!("Could not find @openssl//:openssl binary in runfiles");
}

fn get_base64_str(haystack: &str, label: &str) -> Result<String> {
    let pattern = format!(r"(?msR)^{label}: ([A-Za-z0-9+/=]+)\s*$");
    let rx = Regex::new(&pattern)?;
    let captured = rx
        .captures(haystack)
        .ok_or_else(|| anyhow!("Base64 line for '{label}' not found"))?;
    Ok(captured[1].trim().to_string())
}

fn decode_base64(b64: &str) -> Result<Vec<u8>> {
    let mut bin = Vec::new();
    let mut decoder = Decoder::<Base64>::new(b64.as_bytes())?;
    decoder.decode_to_end(&mut bin)?;
    Ok(bin)
}

fn check_p256_public_key(
    key: &Selectable<SubjectPublicKeyInfo>,
    expected_id: &[u8],
    subject: &Name,
) -> Result<()> {
    let Selectable::Value(SubjectPublicKeyInfo::EcPublicKey(info)) = key else {
        bail!("Expected EC P-256 SubjectPublicKeyInfo, got {key:?}");
    };
    let mut material = Vec::with_capacity(64);
    let x = info.public_key.x.get_value().to_bytes_be();
    let y = info.public_key.y.get_value().to_bytes_be();
    material.extend(std::iter::repeat_n(0u8, 32 - x.len()));
    material.extend(x);
    material.extend(std::iter::repeat_n(0u8, 32 - y.len()));
    material.extend(y);

    let hash = Sha256Digest::hash(&material).to_vec();
    let key_id = &hash[..20];
    if key_id != expected_id {
        bail!(
            "P-256 key ID mismatch: computed {} vs expected {}",
            hex::encode(key_id),
            hex::encode(expected_id)
        );
    }
    let serial_attr = subject[0][&AttributeType::SerialNumber].get_value();
    if serial_attr != &hex::encode(key_id) {
        bail!(
            "Subject serialNumber mismatch: {} vs {}",
            serial_attr,
            hex::encode(key_id)
        );
    }
    Ok(())
}

fn check_openssl_algorithms(
    cert_b64: &str,
    expected_pk_alg: &str,
    expected_sig_alg: &str,
) -> Result<()> {
    let openssl_bin = find_openssl_bin()?;
    let pem = format!("-----BEGIN CERTIFICATE-----\n{cert_b64}\n-----END CERTIFICATE-----\n");
    let mut child = Command::new(openssl_bin)
        .args(["x509", "-text", "-noout"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(pem.as_bytes())?;
    }

    let output = child.wait_with_output()?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("OpenSSL x509 failed to parse PQ_UDS_44: {stderr}");
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let pk_needle = format!("Public Key Algorithm: {expected_pk_alg}");
    let sig_needle = format!("Signature Algorithm: {expected_sig_alg}");
    if !text.contains(&pk_needle) {
        bail!("Certificate missing '{pk_needle}' in OpenSSL output:\n{text}");
    }
    if !text.contains(&sig_needle) {
        bail!("Certificate missing '{sig_needle}' in OpenSSL output:\n{text}");
    }
    Ok(())
}

fn verify_cert_partial_chain(chain_certs_b64: &[&str]) -> Result<()> {
    let chain_certs_pem: Vec<String> = chain_certs_b64
        .iter()
        .map(|b64_cert| {
            format!("-----BEGIN CERTIFICATE-----\n{b64_cert}\n-----END CERTIFICATE-----\n")
        })
        .collect();

    let [root_cert, intermediate_certs @ .., leaf_cert] = &chain_certs_pem[..] else {
        bail!(
            "At least 2 certificates are required to verify chain (got {})",
            chain_certs_b64.len()
        );
    };

    let openssl_bin = find_openssl_bin()?;
    let temp_dir = TempDir::new()?;
    let ca_cert_path = temp_dir.path().join("ca_cert.pem");
    std::fs::write(&ca_cert_path, root_cert)?;

    let intermediate_path = temp_dir.path().join("intermediate_certs.pem");
    std::fs::write(&intermediate_path, intermediate_certs.join("\n"))?;

    let leaf_path = temp_dir.path().join("leaf_cert.pem");
    std::fs::write(&leaf_path, leaf_cert)?;

    let mut args = vec![
        "verify".to_string(),
        "-partial_chain".to_string(),
        "-ignore_critical".to_string(),
        "-show_chain".to_string(),
        "-verbose".to_string(),
        "-CAfile".to_string(),
        ca_cert_path
            .to_str()
            .ok_or_else(|| anyhow!("Invalid CA cert path"))?
            .to_string(),
    ];
    if !intermediate_certs.is_empty() {
        args.push("-untrusted".to_string());
        args.push(
            intermediate_path
                .to_str()
                .ok_or_else(|| anyhow!("Invalid intermediate cert path"))?
                .to_string(),
        );
    }
    args.push(
        leaf_path
            .to_str()
            .ok_or_else(|| anyhow!("Invalid leaf cert path"))?
            .to_string(),
    );

    let output = Command::new(openssl_bin).args(&args).output()?;
    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!(
            "OpenSSL certificate chain verification failed!\nArgs: {args:?}\nStdout: {stdout}\nStderr: {stderr}"
        );
    }
    log::info!(
        "OpenSSL verified {}-certificate chain:\n{}",
        chain_certs_b64.len(),
        String::from_utf8_lossy(&output.stdout)
    );
    Ok(())
}

fn run_test(opts: &Opts, transport: &TransportWrapper) -> Result<()> {
    let uart = transport
        .uart("console")
        .context("failed to open console UART")?;

    if let Some(second_bootstrap) = &opts.second_bootstrap {
        log::info!("Waiting for factory P-256 UDS provisioning helper to finish...");
        let prov_cap = UartConsole::wait_for(
            &*uart,
            r"(?msR).*(PASS!|FAIL!|BFV:[0-9A-Fa-f]{8})$",
            opts.timeout,
        )?;
        if prov_cap[1] != "PASS!" {
            bail!(
                "Factory UDS provisioning helper failed with '{}':\n{}",
                prov_cap[1],
                prov_cap[0]
            );
        }
        log::info!("Bootstrapping assembled ML-DSA ROM_EXT + uds_instantiate image...");
        opts.init.bootstrap.load(transport, second_bootstrap)?;
    }

    log::info!("Waiting for uds_instantiate to construct and store PQ_UDS_44...");
    let first_cap = UartConsole::wait_for(
        &*uart,
        r"(?msR).*(UDS_INSTANTIATE: CREATED|UDS_INSTANTIATE: ALREADY_PRESENT|UDS_INSTANTIATE_ERROR: [^\r\n]+|BFV:[0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    let t_created = Instant::now();
    if first_cap[1] != "UDS_INSTANTIATE: CREATED" {
        bail!(
            "Expected 'UDS_INSTANTIATE: CREATED' on initial instantiation, got '{}':\n{}",
            first_cap[1],
            first_cap[0]
        );
    }
    let first_log = &first_cap[0];

    let pq_uds_b64 = get_base64_str(first_log, "SAVED_PQ_UDS_44")?;
    let saved_cdi1_b64 = get_base64_str(first_log, "SAVED_CDI_1")?;
    let saved_cdi0_b64 = get_base64_str(first_log, "SAVED_CDI_0")?;
    let live_pq_cdi0_b64 = get_base64_str(first_log, "LIVE_PQ_CDI_0")?;
    let live_pq_cdi1_b64 = get_base64_str(first_log, "LIVE_PQ_CDI_1")?;

    let pq_uds_der = decode_base64(&pq_uds_b64)?;
    let saved_cdi1_der = decode_base64(&saved_cdi1_b64)?;
    let saved_cdi0_der = decode_base64(&saved_cdi0_b64)?;
    let live_pq_cdi0_der = decode_base64(&live_pq_cdi0_b64)?;
    let live_pq_cdi1_der = decode_base64(&live_pq_cdi1_b64)?;

    let pq_uds = x509::parse_certificate(&pq_uds_der).context("failed to parse SAVED_PQ_UDS_44")?;
    let saved_cdi1 =
        x509::parse_certificate(&saved_cdi1_der).context("failed to parse SAVED_CDI_1")?;
    let saved_cdi0 =
        x509::parse_certificate(&saved_cdi0_der).context("failed to parse SAVED_CDI_0")?;
    let live_pq_cdi0 =
        x509::parse_certificate(&live_pq_cdi0_der).context("failed to parse LIVE_PQ_CDI_0")?;
    let _live_pq_cdi1 =
        x509::parse_certificate(&live_pq_cdi1_der).context("failed to parse LIVE_PQ_CDI_1")?;

    // Check P-256 CDI_0 and CDI_1 public key IDs.
    check_p256_public_key(
        &saved_cdi0.subject_public_key_info,
        saved_cdi0.subject_key_identifier.get_value(),
        &saved_cdi0.subject,
    )?;
    check_p256_public_key(
        &saved_cdi1.subject_public_key_info,
        saved_cdi1.subject_key_identifier.get_value(),
        &saved_cdi1.subject,
    )?;

    // Check PQ_UDS_44 algorithms, ML-DSA-44 public key size, CA constraints, and linkage.
    check_openssl_algorithms(&pq_uds_b64, "ML-DSA-44", "ecdsa-with-SHA256")?;
    check_openssl_algorithms(&live_pq_cdi0_b64, "ML-DSA-44", "ML-DSA-44")?;
    check_openssl_algorithms(&live_pq_cdi1_b64, "ML-DSA-44", "ML-DSA-44")?;

    let Selectable::Value(SubjectPublicKeyInfo::Mldsa44(_)) = &pq_uds.subject_public_key_info
    else {
        bail!(
            "Expected ML-DSA-44 SubjectPublicKeyInfo in PQ_UDS_44, got {:?}",
            pq_uds.subject_public_key_info
        );
    };
    // Verify the exact ASN.1 DER ML-DSA-44 SubjectPublicKeyInfo header (22 bytes)
    // followed by a non-zero 1312-byte ML-DSA-44 public key in `pq_uds_der`
    // (`ot_certs::x509::parse_certificate` leaves `MldsaPublicKeyInfo.public_key` empty).
    const MLDSA44_SPKI_PREFIX: [u8; 22] = [
        0x30, 0x82, 0x05, 0x32, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04,
        0x03, 0x11, 0x03, 0x82, 0x05, 0x21, 0x00,
    ];
    let spki_pos = pq_uds_der
        .windows(MLDSA44_SPKI_PREFIX.len())
        .position(|w| w == MLDSA44_SPKI_PREFIX)
        .ok_or_else(|| anyhow!("ML-DSA-44 SPKI DER header not found in PQ_UDS_44"))?;
    let mldsa_pk_slice = pq_uds_der
        .get(spki_pos + MLDSA44_SPKI_PREFIX.len()..spki_pos + MLDSA44_SPKI_PREFIX.len() + 1312)
        .ok_or_else(|| anyhow!("PQ_UDS_44 truncated inside 1312-byte ML-DSA-44 public key"))?;
    assert!(
        mldsa_pk_slice.iter().any(|&b| b != 0),
        "ML-DSA-44 public key in PQ_UDS_44 is all zeros"
    );

    let bc = pq_uds
        .basic_constraints
        .as_ref()
        .ok_or_else(|| anyhow!("PQ_UDS_44 missing basic_constraints"))?;
    assert!(*bc.ca.get_value(), "PQ_UDS_44 must have CA=true");

    let ku = pq_uds
        .key_usage
        .as_ref()
        .ok_or_else(|| anyhow!("PQ_UDS_44 missing key_usage"))?;
    assert!(
        *ku.cert_sign.get_value(),
        "PQ_UDS_44 must have keyCertSign=true"
    );

    assert_eq!(
        pq_uds.authority_key_identifier.get_value(),
        saved_cdi1.subject_key_identifier.get_value(),
        "PQ_UDS_44 AKI must match SAVED_CDI_1 SKI"
    );
    assert_eq!(
        pq_uds.issuer, saved_cdi1.subject,
        "PQ_UDS_44 issuer must match SAVED_CDI_1 subject"
    );
    assert_eq!(
        pq_uds.subject_key_identifier.get_value(),
        live_pq_cdi0.authority_key_identifier.get_value(),
        "PQ_UDS_44 SKI must match LIVE_PQ_CDI_0 AKI"
    );
    assert_eq!(
        pq_uds.subject, live_pq_cdi0.issuer,
        "PQ_UDS_44 subject must match LIVE_PQ_CDI_0 issuer"
    );

    let mut expected_serial = pq_uds.subject_key_identifier.get_value().clone();
    expected_serial[0] |= 0x80;
    assert_eq!(
        pq_uds.serial_number.get_value(),
        &BigUint::from_bytes_be(&expected_serial),
        "PQ_UDS_44 serialNumber must match MSB-tweaked SKI"
    );

    if opts.expect_factory_uds {
        let factory_uds_b64 = get_base64_str(first_log, "FACTORY_UDS")?;
        let factory_uds_der = decode_base64(&factory_uds_b64)?;
        let factory_uds =
            x509::parse_certificate(&factory_uds_der).context("failed to parse FACTORY_UDS")?;

        assert_eq!(
            pq_uds.private_extensions, factory_uds.private_extensions,
            "PQ_UDS_44 dice_tcb_info extension must match FACTORY_UDS verbatim"
        );
        let exts = pq_uds
            .private_extensions
            .as_type()
            .ok_or_else(|| anyhow!("Expected structured DiceTcbInfo extension"))?;
        assert_eq!(exts.len(), 1);
        let CertificateExtension::DiceTcbInfo(tcb) = &exts[0];
        assert_eq!(tcb.vendor.get_value(), "OpenTitan");
        assert_eq!(tcb.model.get_value(), "Device");
        assert_eq!(tcb.layer.get_value(), &BigUint::from(0u8));
        let fw_ids = tcb
            .fw_ids
            .as_ref()
            .and_then(|ids| ids.as_type())
            .ok_or_else(|| anyhow!("Expected structured fw_ids in DiceTcbInfo"))?;
        assert_eq!(fw_ids.len(), 4);
        assert_eq!(fw_ids[0].digest.get_value().as_slice(), &[0x11u8; 32]);
        assert_eq!(fw_ids[1].digest.get_value().as_slice(), &[0x22u8; 32]);
        assert_eq!(fw_ids[2].digest.get_value().as_slice(), &[0x33u8; 32]);
        assert_eq!(fw_ids[3].digest.get_value().as_slice(), &[0x44u8; 32]);

        verify_cert_partial_chain(&[
            &factory_uds_b64,
            &saved_cdi0_b64,
            &saved_cdi1_b64,
            &pq_uds_b64,
            &live_pq_cdi0_b64,
            &live_pq_cdi1_b64,
        ])?;
    } else {
        if first_log.contains("FACTORY_UDS:") {
            bail!("Unexpected FACTORY_UDS found on unprovisioned test run");
        }
        let exts = pq_uds
            .private_extensions
            .as_type()
            .ok_or_else(|| anyhow!("Expected empty structured extensions"))?;
        assert!(
            exts.is_empty(),
            "Expected no private_extensions when factory UDS is absent, got {exts:?}"
        );

        verify_cert_partial_chain(&[
            &saved_cdi0_b64,
            &saved_cdi1_b64,
            &pq_uds_b64,
            &live_pq_cdi0_b64,
            &live_pq_cdi1_b64,
        ])?;
    }

    log::info!("Waiting for 10-second sleep, reset, and idempotent second boot...");
    let second_cap = UartConsole::wait_for(
        &*uart,
        r"(?msR).*(UDS_INSTANTIATE: ALREADY_PRESENT|UDS_INSTANTIATE: CREATED|UDS_INSTANTIATE_ERROR: [^\r\n]+|BFV:[0-9A-Fa-f]{8})$",
        opts.timeout,
    )?;
    let sleep_and_reboot_elapsed = t_created.elapsed();
    if second_cap[1] != "UDS_INSTANTIATE: ALREADY_PRESENT" {
        bail!(
            "Expected 'UDS_INSTANTIATE: ALREADY_PRESENT' after reset, got '{}':\n{}",
            second_cap[1],
            second_cap[0]
        );
    }
    if sleep_and_reboot_elapsed < Duration::from_secs(8) {
        bail!(
            "Expected ~10s sleep before reset, but second boot completed after only {sleep_and_reboot_elapsed:?}"
        );
    }
    log::info!("Post-reset idempotency confirmed after {sleep_and_reboot_elapsed:?}!");

    let second_log = &second_cap[0];
    if second_log.contains("Requesting ML-DSA UDS pubkey")
        || second_log.contains("Constructed and endorsed PQ_UDS_44")
    {
        bail!("Second boot unexpectedly re-ran handoff or certificate construction:\n{second_log}");
    }

    assert_eq!(
        decode_base64(&get_base64_str(second_log, "SAVED_PQ_UDS_44")?)?,
        pq_uds_der,
        "SAVED_PQ_UDS_44 changed across reset"
    );
    assert_eq!(
        decode_base64(&get_base64_str(second_log, "SAVED_CDI_1")?)?,
        saved_cdi1_der,
        "SAVED_CDI_1 changed across reset"
    );
    assert_eq!(
        decode_base64(&get_base64_str(second_log, "SAVED_CDI_0")?)?,
        saved_cdi0_der,
        "SAVED_CDI_0 changed across reset"
    );

    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    opts.init.init_logging();
    let transport = opts.init.init_target()?;
    run_test(&opts, &transport)
}
