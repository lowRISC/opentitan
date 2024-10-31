// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::process::Command;

use anyhow::{bail, Context, Result};
use elliptic_curve::SecretKey;
use num_bigint_dig::BigUint;
use openssl::ecdsa::EcdsaSig;
use p256::ecdsa::SigningKey;
use p256::NistP256;

use opentitanlib::crypto::sha256::sha256;
use opentitanlib::util::tmpfilename;
use ot_certs::template::{EcdsaSignature, Signature, Value};
use ot_certs::x509::generate_certificate_from_tbs;
use ot_certs::CertFormat;

/// Execute an openssl invocation, passing the args[] as command line parameters.
///
/// The intended use is openssl x509 certificate verification. cert_num is the
/// number of the certificate in the list of certificates being validated.
fn openssl_command(args: &[&str]) -> Result<()> {
    let o = Command::new("openssl").args(args).output()?;
    if !o.status.success() {
        log::error!(
            "openssl output:\n{}",
            std::str::from_utf8(&o.stderr).unwrap()
        );
        bail!("openssl command {} failed", args[0]);
    }
    Ok(())
}

/// Given a u8 blob containing an x509 certificate perform some rudimentary
/// header correctness checks and return the actual certificate size based on the
/// ASN.1 header length field contents.
pub fn get_cert_size(cert: &[u8]) -> Result<usize> {
    let len = cert.len();

    if len < 4 {
        bail!("Certificate too short {len}");
    }

    if cert[0] != 0x30 || cert[1] != 0x82 {
        bail!("Corrupted ASN.1 header {:02x}{:02x}", cert[0], cert[1]);
    }

    let size = (u16::from_be_bytes([cert[2], cert[3]]) + 4) as usize;

    if size > len {
        bail!("ASN.1 size {} exceeds cert length {}", size, len);
    }
    Ok(size)
}

/// This provides two different certificate signing key representations:
///   1. a SecretKey object in case of fake key or a String object, or
///   2. the ID of the key used by Google Cloud KMS.
pub enum CertEndorsementKey {
    LocalKey(SecretKey<NistP256>),
    CkmsKey(String),
}

/// Parses an X.509 ASN.1 DER encoded certificate, signs it with the specified
/// key, and attaches a signature to it.
pub fn parse_and_endorse_x509_cert(tbs: Vec<u8>, key: &CertEndorsementKey) -> Result<Vec<u8>> {
    match key {
        CertEndorsementKey::CkmsKey(key_id) => parse_and_endorse_x509_cert_ckms(tbs, key_id),
        CertEndorsementKey::LocalKey(ca_sk) => parse_and_endorse_x509_cert_local(tbs, ca_sk),
    }
}

fn parse_and_endorse_x509_cert_local(tbs: Vec<u8>, ca_sk: &SecretKey<NistP256>) -> Result<Vec<u8>> {
    // Hash and sign the TBS.
    let tbs_digest = sha256(&tbs);
    let signing_key = SigningKey::from(ca_sk);
    let (tbs_signature, _) = signing_key.sign_prehash_recoverable(&tbs_digest.to_be_bytes())?;
    let (r, s) = tbs_signature.split_bytes();

    // Reformat the signature.
    let signature = Signature::EcdsaWithSha256 {
        value: Some(EcdsaSignature {
            r: Value::Literal(BigUint::from_bytes_be(&r)),
            s: Value::Literal(BigUint::from_bytes_be(&s)),
        }),
    };

    // Generate the (endorsed) certificate.
    generate_certificate_from_tbs(tbs, &signature)
}

fn parse_and_endorse_x509_cert_ckms(tbs: Vec<u8>, ckms_key_id: &str) -> Result<Vec<u8>> {
    // Let openssl hash and sign the TBS.
    let base_name = tmpfilename("cert_signing");
    let binding_tbs = base_name.to_owned() + ".tbs";
    let binding_sig = base_name.to_owned() + ".sig";
    let tbs_filename = binding_tbs.as_str();
    let sig_filename = binding_sig.as_str();

    // Save TBS in a file.
    let mut file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(tbs_filename)
        .context("failed to open tbs file")?;
    file.write_all(&tbs)?;
    drop(file);

    let binding_key = String::from("pkcs11:object=") + ckms_key_id;
    openssl_command(&[
        "dgst",
        "-sha256",
        "-engine",
        "pkcs11",
        "-keyform",
        "engine",
        "-sign",
        binding_key.as_str(),
        "-out",
        sig_filename,
        tbs_filename,
    ])
    .context("openssl failed to sign certificate digest")?;

    // Read the signature represented as an ASN.1 object.
    file = OpenOptions::new().read(true).open(sig_filename)?;
    let mut asn1_sig = Vec::new();
    file.read_to_end(&mut asn1_sig)?;
    drop(file);

    // Parse the ASN.1 string into signature components.
    let ecdsa_sig =
        EcdsaSig::from_der(&asn1_sig).context("cannot extract ECDSA signature from blob")?;

    let signature = Signature::EcdsaWithSha256 {
        value: Some(EcdsaSignature {
            r: Value::Literal(BigUint::from_bytes_be(&ecdsa_sig.r().to_vec())),
            s: Value::Literal(BigUint::from_bytes_be(&ecdsa_sig.s().to_vec())),
        }),
    };

    fs::remove_file(tbs_filename).context("failed to remove tbs file")?;
    fs::remove_file(sig_filename).context("failed to remove signature file")?;

    // Generate the (endorsed) certificate.
    generate_certificate_from_tbs(tbs, &signature)
}

fn write_cert_to_temp_pem_file(der_cert_bytes: &[u8], base_filename: &str) -> Result<String> {
    // Build temp file names for DER and PEM cert files.
    let base_name = tmpfilename(base_filename);
    let binding_der = base_name.to_owned() + ".der";
    let binding_pem = base_name.to_owned() + ".pem";
    let der_filename = binding_der.as_str();
    let pem_filename = binding_pem.as_str();

    // Write DER bytes to the tmp file.
    let size = get_cert_size(der_cert_bytes)?;
    let mut file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(der_filename)
        .context(format!(
            "failed to open temporary DER file: {:?}",
            der_filename
        ))?;
    file.write_all(&der_cert_bytes[0..size])?;
    drop(file);

    // Convert the DER cert file to a PEM cert file.
    openssl_command(&[
        "x509",
        "-out",
        pem_filename,
        "-in",
        der_filename,
        "-inform",
        "der",
    ])
    .context(format!(
        "failed to covert DER file ({:?}) to PEM",
        der_filename
    ))?;

    // Cleanup the intermediate DER file.
    fs::remove_file(der_filename).context("failed to remove der file")?;

    Ok(binding_pem)
}

/// Container for an endorsed certificate.
///
/// This is used to pass a collection of endorsed certificates, along with metadata,
/// to various functions that check the certificates validate properly with third-party
/// tools.
#[derive(Clone, Debug)]
pub struct EndorsedCert {
    pub format: CertFormat,
    pub name: String,
    pub bytes: Vec<u8>,
    pub ignore_critical: bool,
}

/// Validate a chain of X.509 certificates against a provided CA certificate.
///
/// A chain of X.509 certificates are validated against the CA using the 'openssl verify ...' command.
///
/// Arguments:
/// * ca_pem - The file name of the CA certificate saved in PEM format.
/// * cert_chain - A slice of EndorsedCert objects representing a chain ordered from root to leaf.
pub fn validate_cert_chain(ca_pem: &str, cert_chain: &[EndorsedCert]) -> Result<()> {
    let mut ignore_critical = false;

    // Create temp CA PEM file.
    let tmp_ca_pem_filename_binding = tmpfilename("tmp_ca_chain.pem");
    let tmp_ca_pem_filename = tmp_ca_pem_filename_binding.as_str();
    fs::copy(ca_pem, tmp_ca_pem_filename)?;

    // Iterate over leaf certs.
    let mut tmp_leaf_cert_pem_filename: String = "".to_string();
    for cert in cert_chain.iter() {
        // Overwrite the current leaf cert PEM file.
        tmp_leaf_cert_pem_filename = write_cert_to_temp_pem_file(&cert.bytes, "leaf")?;

        // If a cert in the chain has a critical custom extension, we need to
        // tell OpenSSL to ignore it from here out. The `-ignore_critical` flag
        // is required to verify DICE certificates that use the DiceTcbInfo
        // custom extension that is a TCG standard (critical) extension that is
        // not recognized by OpenSSL.
        if cert.ignore_critical {
            ignore_critical = true;
        }

        // Verify the cert chain up to the current leaf cert.
        let mut args = vec!["verify", "-CAfile", tmp_ca_pem_filename];
        if ignore_critical {
            args.push("-ignore_critical");
        }
        args.push(tmp_leaf_cert_pem_filename.as_str());
        openssl_command(&args).context(format!(
            "failed to verify a certificate chain at {:?} cert",
            cert.name.as_str()
        ))?;

        // Append the current leaf cert to the CA PEM file.
        let mut tmp_ca_file = OpenOptions::new().append(true).open(tmp_ca_pem_filename)?;
        let leaf_cert_pem_contents = fs::read(tmp_leaf_cert_pem_filename.as_str())?;
        tmp_ca_file.write_all(&leaf_cert_pem_contents)?;
        drop(tmp_ca_file);
    }

    // Cleanup the temp PEM cert files.
    fs::remove_file(tmp_ca_pem_filename).context("failed to remove temp CA PEM file")?;
    fs::remove_file(tmp_leaf_cert_pem_filename.as_str())
        .context("failed to remove temp leaf PEM file")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validate_good() {
        let ca_pem = "./sw/device/silicon_creator/manuf/keys/fake/fake_ca.pem";
        // The below byte blob is a proper TPM EK certificate generated during test runs.
        let mut cert0 = EndorsedCert {
            format: CertFormat::X509,
            name: "cert0".to_string(),
            ignore_critical: false,
            bytes: vec![
                48, 130, 2, 30, 48, 130, 1, 195, 160, 3, 2, 1, 2, 2, 21, 0, 254, 88, 74, 231, 83,
                121, 12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8,
                42, 134, 72, 206, 61, 4, 3, 2, 48, 98, 49, 11, 48, 9, 6, 3, 85, 4, 6, 19, 2, 85,
                83, 49, 11, 48, 9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3, 85, 4, 10,
                12, 6, 71, 111, 111, 103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11, 69,
                110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 49, 31, 48, 29, 6, 3, 85, 4, 3,
                12, 22, 71, 111, 111, 103, 108, 101, 32, 69, 110, 103, 105, 110, 101, 101, 114,
                105, 110, 103, 32, 73, 67, 65, 48, 34, 24, 15, 50, 48, 50, 51, 48, 49, 48, 49, 48,
                48, 48, 48, 48, 48, 90, 24, 15, 50, 48, 53, 48, 48, 49, 48, 49, 48, 48, 48, 48, 48,
                48, 90, 48, 91, 49, 11, 48, 9, 6, 3, 85, 4, 6, 19, 2, 85, 83, 49, 11, 48, 9, 6, 3,
                85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3, 85, 4, 10, 12, 6, 71, 111, 111, 103,
                108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11, 69, 110, 103, 105, 110, 101,
                101, 114, 105, 110, 103, 49, 24, 48, 22, 6, 3, 85, 4, 3, 12, 15, 79, 84, 32, 84,
                105, 53, 48, 32, 84, 80, 77, 32, 67, 69, 75, 48, 89, 48, 19, 6, 7, 42, 134, 72,
                206, 61, 2, 1, 6, 8, 42, 134, 72, 206, 61, 3, 1, 7, 3, 66, 0, 4, 75, 36, 92, 59,
                242, 87, 205, 181, 243, 64, 67, 94, 55, 61, 212, 203, 207, 248, 209, 47, 241, 223,
                36, 175, 158, 22, 108, 92, 42, 51, 192, 39, 17, 132, 53, 214, 61, 160, 143, 166,
                32, 42, 135, 52, 200, 241, 109, 217, 83, 200, 241, 175, 120, 194, 83, 63, 228, 215,
                73, 172, 68, 56, 35, 128, 163, 89, 48, 87, 48, 15, 6, 3, 85, 29, 15, 1, 1, 255, 4,
                5, 3, 3, 7, 4, 0, 48, 34, 6, 3, 85, 29, 35, 1, 1, 0, 4, 24, 48, 22, 128, 20, 254,
                88, 74, 231, 83, 121, 12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209,
                18, 48, 32, 6, 3, 85, 29, 14, 1, 1, 0, 4, 22, 4, 20, 254, 88, 74, 231, 83, 121, 12,
                253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134,
                72, 206, 61, 4, 3, 2, 3, 73, 0, 48, 70, 2, 33, 0, 240, 38, 63, 102, 107, 249, 121,
                172, 4, 241, 107, 165, 35, 37, 171, 90, 48, 66, 147, 139, 113, 70, 180, 79, 150,
                47, 104, 12, 150, 152, 148, 164, 2, 33, 0, 230, 94, 91, 132, 244, 223, 193, 68, 55,
                152, 134, 144, 23, 170, 127, 50, 192, 212, 197, 249, 142, 111, 169, 74, 208, 28,
                153, 239, 199, 225, 252, 3,
            ],
        };

        // Verify that the certificate validation succeeds.
        assert!(validate_cert_chain(ca_pem, &[cert0.clone()]).is_ok());

        // Corrupt the fist certificate in the chain and verify that the
        // certificate validation fails.
        let bad_value = cert0.bytes.pop().unwrap() + 1;
        cert0.bytes.push(bad_value);
        assert!(validate_cert_chain(ca_pem, &[cert0.clone()]).is_err());
    }
}
