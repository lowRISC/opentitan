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

/// Validate a chain of X.509 certificates using 'openssl verify ...' command.
///
/// Arguments:
/// * ca_pem - The file name of the CA certificate saved in PEM format.
/// * certs  - A vector of certificate binary blobs.
pub fn validate_certs_chain(ca_pem: &str, certs: &[&Vec<u8>]) -> Result<()> {
    let base_name = tmpfilename("cert_validation");
    let binding_der = base_name.to_owned() + ".der";
    let binding_pem = base_name.to_owned() + ".pem";

    let der_filename = binding_der.as_str();
    let pem_filename = binding_pem.as_str();

    for cert in certs.iter() {
        let size = get_cert_size(cert)?;
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(der_filename)
            .context("failed to open temporary der file")?;
        file.write_all(&cert[0..size])?;
        drop(file);

        openssl_command(&[
            "x509",
            "-out",
            pem_filename,
            "-in",
            der_filename,
            "-inform",
            "der",
        ])
        .context("failed to covert DER to PEM")?;

        // Validate with the fake CA certificate.
        openssl_command(&["verify", "-CAfile", ca_pem, pem_filename])
            .context("failed to verify a certificate chain")?;
    }

    fs::remove_file(der_filename).context("failed to remove der file")?;
    fs::remove_file(pem_filename).context("failed to remove pem file")?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validate_good() {
        let ca_pem = "./sw/device/silicon_creator/manuf/keys/fake/fake_ca.pem";
        // The below byte blobs are proper TPM EK, TPM CEK and TPM CIK certificates
        // generated during test runs.
        let mut cert0: Vec<u8> = vec![
            48, 130, 2, 30, 48, 130, 1, 195, 160, 3, 2, 1, 2, 2, 21, 0, 254, 88, 74, 231, 83, 121,
            12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134,
            72, 206, 61, 4, 3, 2, 48, 98, 49, 11, 48, 9, 6, 3, 85, 4, 6, 19, 2, 85, 83, 49, 11, 48,
            9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3, 85, 4, 10, 12, 6, 71, 111, 111,
            103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11, 69, 110, 103, 105, 110, 101,
            101, 114, 105, 110, 103, 49, 31, 48, 29, 6, 3, 85, 4, 3, 12, 22, 71, 111, 111, 103,
            108, 101, 32, 69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 32, 73, 67, 65, 48,
            34, 24, 15, 50, 48, 50, 51, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 24, 15, 50, 48,
            53, 48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 48, 91, 49, 11, 48, 9, 6, 3, 85, 4,
            6, 19, 2, 85, 83, 49, 11, 48, 9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3,
            85, 4, 10, 12, 6, 71, 111, 111, 103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11,
            69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 49, 24, 48, 22, 6, 3, 85, 4, 3,
            12, 15, 79, 84, 32, 84, 105, 53, 48, 32, 84, 80, 77, 32, 67, 69, 75, 48, 89, 48, 19, 6,
            7, 42, 134, 72, 206, 61, 2, 1, 6, 8, 42, 134, 72, 206, 61, 3, 1, 7, 3, 66, 0, 4, 75,
            36, 92, 59, 242, 87, 205, 181, 243, 64, 67, 94, 55, 61, 212, 203, 207, 248, 209, 47,
            241, 223, 36, 175, 158, 22, 108, 92, 42, 51, 192, 39, 17, 132, 53, 214, 61, 160, 143,
            166, 32, 42, 135, 52, 200, 241, 109, 217, 83, 200, 241, 175, 120, 194, 83, 63, 228,
            215, 73, 172, 68, 56, 35, 128, 163, 89, 48, 87, 48, 15, 6, 3, 85, 29, 15, 1, 1, 255, 4,
            5, 3, 3, 7, 4, 0, 48, 34, 6, 3, 85, 29, 35, 1, 1, 0, 4, 24, 48, 22, 128, 20, 254, 88,
            74, 231, 83, 121, 12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48,
            32, 6, 3, 85, 29, 14, 1, 1, 0, 4, 22, 4, 20, 254, 88, 74, 231, 83, 121, 12, 253, 134,
            1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134, 72, 206, 61, 4,
            3, 2, 3, 73, 0, 48, 70, 2, 33, 0, 240, 38, 63, 102, 107, 249, 121, 172, 4, 241, 107,
            165, 35, 37, 171, 90, 48, 66, 147, 139, 113, 70, 180, 79, 150, 47, 104, 12, 150, 152,
            148, 164, 2, 33, 0, 230, 94, 91, 132, 244, 223, 193, 68, 55, 152, 134, 144, 23, 170,
            127, 50, 192, 212, 197, 249, 142, 111, 169, 74, 208, 28, 153, 239, 199, 225, 252, 3,
        ];
        let cert1: Vec<u8> = vec![
            48, 130, 2, 30, 48, 130, 1, 196, 160, 3, 2, 1, 2, 2, 21, 0, 254, 88, 74, 231, 83, 121,
            12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134,
            72, 206, 61, 4, 3, 2, 48, 98, 49, 11, 48, 9, 6, 3, 85, 4, 6, 19, 2, 85, 83, 49, 11, 48,
            9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3, 85, 4, 10, 12, 6, 71, 111, 111,
            103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11, 69, 110, 103, 105, 110, 101,
            101, 114, 105, 110, 103, 49, 31, 48, 29, 6, 3, 85, 4, 3, 12, 22, 71, 111, 111, 103,
            108, 101, 32, 69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 32, 73, 67, 65, 48,
            34, 24, 15, 50, 48, 50, 51, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 24, 15, 50, 48,
            53, 48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 48, 92, 49, 12, 48, 10, 6, 3, 85,
            4, 6, 19, 3, 85, 83, 65, 49, 11, 48, 9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13,
            6, 3, 85, 4, 10, 12, 6, 71, 111, 111, 103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11,
            12, 11, 69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 49, 24, 48, 22, 6, 3, 85,
            4, 3, 12, 15, 79, 84, 32, 84, 105, 53, 48, 32, 84, 80, 77, 32, 67, 73, 75, 48, 89, 48,
            19, 6, 7, 42, 134, 72, 206, 61, 2, 1, 6, 8, 42, 134, 72, 206, 61, 3, 1, 7, 3, 66, 0, 4,
            23, 2, 208, 197, 46, 115, 49, 121, 86, 105, 156, 23, 214, 86, 136, 68, 165, 14, 47, 42,
            160, 138, 115, 31, 18, 244, 254, 181, 94, 24, 82, 33, 10, 216, 173, 10, 33, 196, 106,
            167, 143, 159, 150, 126, 119, 105, 95, 94, 173, 171, 168, 79, 117, 84, 122, 225, 159,
            199, 136, 15, 158, 63, 203, 182, 163, 89, 48, 87, 48, 15, 6, 3, 85, 29, 15, 1, 1, 255,
            4, 5, 3, 3, 7, 4, 0, 48, 34, 6, 3, 85, 29, 35, 1, 1, 0, 4, 24, 48, 22, 128, 20, 254,
            88, 74, 231, 83, 121, 12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18,
            48, 32, 6, 3, 85, 29, 14, 1, 1, 0, 4, 22, 4, 20, 254, 88, 74, 231, 83, 121, 12, 253,
            134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134, 72, 206,
            61, 4, 3, 2, 3, 72, 0, 48, 69, 2, 33, 0, 168, 91, 65, 85, 113, 153, 190, 161, 53, 216,
            6, 110, 144, 236, 235, 241, 120, 29, 68, 169, 78, 127, 249, 176, 134, 165, 37, 201, 53,
            153, 67, 23, 2, 32, 43, 141, 139, 0, 178, 8, 79, 249, 88, 149, 79, 111, 71, 89, 118,
            215, 184, 234, 135, 64, 141, 49, 185, 235, 162, 11, 75, 151, 237, 211, 126, 3,
        ];
        let cert2: Vec<u8> = vec![
            48, 130, 2, 120, 48, 130, 2, 31, 160, 3, 2, 1, 2, 2, 21, 0, 254, 88, 74, 231, 83, 121,
            12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134,
            72, 206, 61, 4, 3, 2, 48, 98, 49, 11, 48, 9, 6, 3, 85, 4, 6, 19, 2, 85, 83, 49, 11, 48,
            9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13, 6, 3, 85, 4, 10, 12, 6, 71, 111, 111,
            103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11, 12, 11, 69, 110, 103, 105, 110, 101,
            101, 114, 105, 110, 103, 49, 31, 48, 29, 6, 3, 85, 4, 3, 12, 22, 71, 111, 111, 103,
            108, 101, 32, 69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 32, 73, 67, 65, 48,
            34, 24, 15, 50, 48, 50, 51, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 24, 15, 50, 48,
            53, 48, 48, 49, 48, 49, 48, 48, 48, 48, 48, 48, 90, 48, 91, 49, 12, 48, 10, 6, 3, 85,
            4, 6, 19, 3, 85, 83, 65, 49, 11, 48, 9, 6, 3, 85, 4, 8, 12, 2, 67, 65, 49, 15, 48, 13,
            6, 3, 85, 4, 10, 12, 6, 71, 111, 111, 103, 108, 101, 49, 20, 48, 18, 6, 3, 85, 4, 11,
            12, 11, 69, 110, 103, 105, 110, 101, 101, 114, 105, 110, 103, 49, 23, 48, 21, 6, 3, 85,
            4, 3, 12, 14, 79, 84, 32, 84, 105, 53, 48, 32, 84, 80, 77, 32, 69, 75, 48, 89, 48, 19,
            6, 7, 42, 134, 72, 206, 61, 2, 1, 6, 8, 42, 134, 72, 206, 61, 3, 1, 7, 3, 66, 0, 4, 35,
            64, 229, 133, 12, 236, 28, 25, 38, 236, 216, 29, 0, 26, 245, 51, 42, 42, 25, 195, 175,
            11, 91, 100, 98, 246, 216, 83, 114, 149, 55, 0, 42, 239, 136, 47, 16, 228, 64, 214, 34,
            187, 164, 143, 120, 232, 148, 219, 93, 47, 206, 9, 22, 74, 236, 168, 12, 71, 249, 167,
            144, 83, 247, 113, 163, 129, 180, 48, 129, 177, 48, 15, 6, 3, 85, 29, 19, 1, 1, 255, 4,
            5, 48, 3, 1, 1, 0, 48, 71, 6, 3, 85, 29, 17, 1, 1, 0, 4, 61, 48, 59, 164, 57, 48, 55,
            49, 18, 48, 16, 6, 5, 103, 129, 5, 2, 1, 12, 7, 78, 117, 118, 111, 116, 111, 110, 49,
            15, 48, 13, 6, 5, 103, 129, 5, 2, 2, 12, 4, 84, 105, 53, 48, 49, 16, 48, 14, 6, 5, 103,
            129, 5, 2, 3, 12, 5, 48, 46, 48, 46, 49, 48, 15, 6, 3, 85, 29, 15, 1, 1, 255, 4, 5, 3,
            3, 7, 4, 0, 48, 34, 6, 3, 85, 29, 35, 1, 1, 0, 4, 24, 48, 22, 128, 20, 254, 88, 74,
            231, 83, 121, 12, 253, 134, 1, 163, 18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 32, 6,
            3, 85, 29, 14, 1, 1, 0, 4, 22, 4, 20, 254, 88, 74, 231, 83, 121, 12, 253, 134, 1, 163,
            18, 251, 50, 211, 193, 184, 34, 209, 18, 48, 10, 6, 8, 42, 134, 72, 206, 61, 4, 3, 2,
            3, 71, 0, 48, 68, 2, 32, 59, 137, 187, 122, 144, 29, 233, 183, 34, 136, 15, 198, 224,
            76, 4, 142, 107, 206, 21, 193, 69, 82, 158, 66, 52, 5, 7, 143, 0, 128, 166, 12, 2, 32,
            47, 221, 22, 12, 155, 16, 223, 208, 245, 225, 214, 31, 180, 72, 22, 35, 219, 11, 15,
            135, 6, 228, 81, 120, 178, 122, 236, 127, 160, 134, 84, 95,
        ];

        // Verify that the certificate validation succeeds.
        assert!(validate_certs_chain(ca_pem, &[&cert0, &cert1, &cert2]).is_ok());

        // Corrupt the fist certificate in the chain and verify that the
        // certificate validation fails.
        let bad_value = cert0.pop().unwrap() + 1;
        cert0.push(bad_value);
        assert!(validate_certs_chain(ca_pem, &[&cert0, &cert1, &cert2]).is_err());
    }
}
