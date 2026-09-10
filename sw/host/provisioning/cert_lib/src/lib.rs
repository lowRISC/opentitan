// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::env;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::Command;

use anyhow::{Context, Result, bail, ensure};
use base64ct::{Base64, Encoding};
use elliptic_curve::SecretKey;
use hwtrust::dice::ChainForm;
use hwtrust::session::Session;
use zeroize::Zeroize;

pub struct MlDsaSeed {
    pkey: openssl::pkey::PKey<openssl::pkey::Private>,
}

use num_bigint_dig::BigUint;
use openssl::ecdsa::EcdsaSig;
use p256::NistP256;
use p256::ecdsa::SigningKey as EcdsaSigningKey;
use serde::{Deserialize, Serialize, Serializer};

use opentitanlib::crypto::sha256::Sha256Digest;
use opentitanlib::util::tmpfilename;
use ot_certs::CertFormat;
use ot_certs::cbor;
use ot_certs::template::{EcdsaSignature, Signature, Value};
use ot_certs::x509::generate_certificate_from_tbs;
use runfiles::{Runfiles, rlocation};

/// Certificate Authority key type.
#[derive(Debug, Clone, Deserialize)]
pub enum CaKeyType {
    Raw,
    Token,
}

pub enum RawKeyType {
    EcdsaKey(SecretKey<NistP256>),
    MldsaSeed(MlDsaSeed),
}

#[derive(Debug, Clone)]
pub enum TokenKeyType {
    EcdsaKey(String),
    MldsaKey(String),
}

/// Certificate Authority key input formats.
///
/// The following private key representations are supported:
///   1. RawKey: provided as a file path pointing to a DER encoded key file.
///   2. TokenKey: provided as a PKCS#11 token key/object identifier string.
pub enum CaKey {
    RawKey(RawKeyType),
    TokenKey(TokenKeyType),
}

/// Certificate Authority (CA) parameters.
#[derive(Debug, Clone, Deserialize)]
pub struct CaConfig {
    /// CA certificate PEM file path.
    pub certificate: PathBuf,
    /// CA certificate key ID (160-bit hex string serial number used in CA certificate).
    pub key_id: String,
    /// CA key type.
    pub key_type: CaKeyType,
    /// CA key (file path to raw key DER file or Cloud KMS key ID).
    pub key: String,
}

fn run(runfile_path: &str, args: &[&str]) -> Result<Vec<u8>> {
    let r = Runfiles::create().context("failed to initialize runfiles")?;
    let bin = rlocation!(r, runfile_path)
        .filter(|p| p.exists())
        .ok_or_else(|| {
            anyhow::anyhow!("Could not find hermetic binary {runfile_path:?} in runfiles")
        })?;
    let o = Command::new(bin).args(args).output()?;
    if !o.status.success() {
        log::error!(
            "{runfile_path} output:\n{}",
            std::str::from_utf8(&o.stderr).unwrap_or("<invalid utf8>")
        );
        bail!("{runfile_path} command {:?} failed", args);
    }
    Ok(o.stdout)
}

/// Execute an openssl invocation, passing the args[] as command line parameters.
fn openssl_command(args: &[&str]) -> Result<Vec<u8>> {
    run("openssl/openssl", args)
}

/// Execute an hsmtool invocation, passing the args[] as command line parameters.
fn hsmtool_command(args: &[&str]) -> Result<Vec<u8>> {
    run("lowrisc_opentitan/sw/host/hsmtool/hsmtool", args)
}

impl MlDsaSeed {
    /// Reads an ML-DSA PKCS#8 DER private key from a file.
    pub fn read_pkcs8_der_file(path: &str) -> Result<Self> {
        let mut der = fs::read(path).with_context(|| format!("failed to read key file {path}"))?;
        let res = openssl::pkey::PKey::private_key_from_der(&der)
            .context("failed to parse ML-DSA-87 PKCS#8 private key in OpenSSL");
        der.zeroize();
        Ok(Self { pkey: res? })
    }

    /// Reads an ML-DSA PKCS#8 DER private key from an HSM Elementary File (CKO_DATA object) using `hsmtool object show`.
    pub fn read_from_hsm_ef(label: &str) -> Result<Self> {
        let output = hsmtool_command(&[
            "--format",
            "json",
            "object",
            "show",
            "--label",
            label,
            "--redact=false",
        ])
        .context("hsmtool object show failed")?;

        #[derive(serde::Deserialize)]
        struct ShowResult {
            objects: Vec<std::collections::HashMap<String, serde_json::Value>>,
        }

        let result: ShowResult =
            serde_json::from_slice(&output).context("failed to parse hsmtool json output")?;
        if result.objects.is_empty() {
            bail!("No object found in HSM with label '{}'", label);
        }
        let obj = &result.objects[0];
        let class = obj
            .get("CKA_CLASS")
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                anyhow::anyhow!("CKA_CLASS missing or not a string for object '{}'", label)
            })?;
        ensure!(
            class == "CKO_DATA",
            "Expected CKO_DATA object for ML-DSA key '{}', got '{}'",
            label,
            class
        );
        let val = obj
            .get("CKA_VALUE")
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                anyhow::anyhow!("CKA_VALUE missing or not a string for object '{}'", label)
            })?;

        let hex_clean = val.replace(':', "");
        let mut bytes = hex::decode(&hex_clean)
            .with_context(|| format!("failed to decode hex key from HSM object '{}'", label))?;

        let res = openssl::pkey::PKey::private_key_from_der(&bytes)
            .context("failed to parse ML-DSA-87 PKCS#8 private key in OpenSSL");
        bytes.zeroize();
        Ok(Self { pkey: res? })
    }

    /// Endorses an X.509 certificate given its TBS (To-Be-Signed) bytes.
    pub fn endorse_x509_cert(&self, tbs: &[u8]) -> Result<Vec<u8>> {
        let mut signer = openssl::sign::Signer::new_without_digest(&self.pkey)
            .context("failed to initialize ML-DSA-87 signer")?;
        let sig_bytes = signer
            .sign_oneshot_to_vec(tbs)
            .context("failed to sign TBS with ML-DSA-87")?;

        let signature = Signature::Mldsa87 {
            value: Some(Value::Literal(sig_bytes)),
        };

        generate_certificate_from_tbs(tbs.to_vec(), &signature)
    }
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

/// Parses an X.509 ASN.1 DER encoded certificate, signs it with the specified
/// key, and attaches a signature to it.
pub fn parse_and_endorse_x509_cert(tbs: Vec<u8>, key: &CaKey) -> Result<Vec<u8>> {
    match key {
        CaKey::TokenKey(TokenKeyType::EcdsaKey(key_id)) => {
            parse_and_endorse_x509_cert_token(tbs, key_id)
        }
        CaKey::TokenKey(TokenKeyType::MldsaKey(key_id)) => {
            parse_and_endorse_x509_mldsa_cert_token(tbs, key_id)
        }
        CaKey::RawKey(RawKeyType::EcdsaKey(sk)) => parse_and_endorse_x509_cert_raw(tbs, sk),
        CaKey::RawKey(RawKeyType::MldsaSeed(esk)) => esk.endorse_x509_cert(&tbs),
    }
}

fn parse_and_endorse_x509_mldsa_cert_token(tbs: Vec<u8>, key_id: &str) -> Result<Vec<u8>> {
    // Currently, the ML-DSA CA key is stored in the HSM as an elementary file (CKO_DATA object
    // containing the PKCS#8 DER-encoded key), so we load it via hsmtool object show and endorse via RawKey.
    // When HSM token signing for ML-DSA is directly supported via PKCS#11, sign via token directly.
    let seed = MlDsaSeed::read_from_hsm_ef(key_id)?;
    seed.endorse_x509_cert(&tbs)
}

fn parse_and_endorse_x509_cert_raw(tbs: Vec<u8>, ca_sk: &SecretKey<NistP256>) -> Result<Vec<u8>> {
    // Hash and sign the TBS.
    let tbs_digest = Sha256Digest::hash(&tbs);
    let signing_key = EcdsaSigningKey::from(ca_sk);
    let (tbs_signature, _) = signing_key.sign_prehash_recoverable(tbs_digest.as_ref())?;
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

fn parse_and_endorse_x509_cert_token(tbs: Vec<u8>, key_id: &str) -> Result<Vec<u8>> {
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

    let token_pin = env::var("PKCS11_TOKEN_PIN")?;
    let key_uri = format!("pkcs11:pin-value={};object={}", token_pin, key_id);
    openssl_command(&[
        "dgst",
        "-sha256",
        "-engine",
        "pkcs11",
        "-keyform",
        "engine",
        "-sign",
        key_uri.as_str(),
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

fn write_cert_to_temp_pem_file(der_cert_bytes: &[u8], base_name: &str) -> Result<String> {
    // Build temp file names for DER and PEM cert files.
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

fn serialize_certificate<S: Serializer>(cert: &Vec<u8>, serializer: S) -> Result<S::Ok, S::Error> {
    let s = Base64::encode_string(cert.as_slice());
    serializer.serialize_str(&s)
}

/// Container for an endorsed certificate.
///
/// This is used to pass a collection of endorsed certificates, along with metadata,
/// to various functions that check the certificates validate properly with third-party
/// tools.
#[derive(Clone, Debug, Serialize)]
pub struct EndorsedCert {
    pub format: CertFormat,
    pub name: String,
    #[serde(serialize_with = "serialize_certificate")]
    pub bytes: Vec<u8>,
    pub ignore_critical: bool,
}

/// Validate a CWT DICE chain.
///
/// A CWT DICE chain is validated using 'hwtrust'.
///
/// Arguments:
/// * cert_chain - A slice of EndorsedCert objects representing a chain ordered from root to leaf.
pub fn validate_cwt_dice_chain(cert_chain: &[EndorsedCert]) -> Result<()> {
    if !cert_chain
        .iter()
        .all(|c| matches!(c.format, CertFormat::Cwt))
    {
        bail!(
            "A non-CWT cert found in the CWT cert chain. {:?}",
            cert_chain
        );
    }

    let header = cbor::array_header(
        cert_chain
            .len()
            .try_into()
            .context("Cannot convert the size of the cert chain from usize to u64.")?,
    );

    let mut bytes = header;

    for cert in cert_chain {
        bytes.append(&mut cert.bytes.clone());
    }

    let session = Session::default();
    let chain = ChainForm::from_cbor(&session, &bytes).context("Not a valid CWT DICE chain.")?;

    if matches!(chain, ChainForm::Degenerate(_)) {
        bail!("Degenerate CWT DICE chain.");
    }

    Ok(())
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
    let tmp_dir = tempfile::tempdir().context("failed to create temporary directory")?;
    let tmp_ca_pem = tmp_dir.path().join("tmp_ca_chain.pem");
    let tmp_ca_pem_filename = tmp_ca_pem.to_str().unwrap();
    let tmp_leaf_base = tmp_dir.path().join("leaf");
    fs::copy(ca_pem, tmp_ca_pem_filename)?;

    // Iterate over leaf certs.
    for cert in cert_chain.iter() {
        // Overwrite the current leaf cert PEM file.
        let tmp_leaf_cert_pem_filename =
            write_cert_to_temp_pem_file(&cert.bytes, tmp_leaf_base.to_str().unwrap())?;

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

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validate_good() {
        let ca_pem = "./sw/device/silicon_creator/manuf/keys/fake/ext_ca.pem";
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

    fn run_mldsa_ca_test(ca_pem: &str, ca_key: &str, key: &CaKey) {
        let tmp_dir = tempfile::tempdir().unwrap();
        let csr_path = tmp_dir.path().join("leaf.csr");
        let leaf_key_path = tmp_dir.path().join("leaf_key.pem");
        let leaf_cert_path = tmp_dir.path().join("leaf_cert.der");

        let csr_str = csr_path.to_str().unwrap();
        let leaf_key_str = leaf_key_path.to_str().unwrap();
        let leaf_cert_str = leaf_cert_path.to_str().unwrap();

        // 1. Generate a test CSR for a leaf certificate
        openssl_command(&[
            "req",
            "-new",
            "-newkey",
            "ML-DSA-87",
            "-subj",
            "/C=US/ST=CA/O=OpenTitan/CN=PQ_UDS_TEST",
            "-out",
            csr_str,
            "-keyout",
            leaf_key_str,
            "-nodes",
        ])
        .expect("openssl req should succeed");

        // 2. Issue a leaf certificate with the CA key to get a valid TBS
        openssl_command(&[
            "x509",
            "-req",
            "-in",
            csr_str,
            "-CA",
            ca_pem,
            "-CAkey",
            ca_key,
            "-CAkeyform",
            "der",
            "-out",
            leaf_cert_str,
            "-outform",
            "der",
            "-days",
            "365",
        ])
        .expect("openssl x509 issue should succeed");

        let leaf_der_bytes = fs::read(&leaf_cert_path).expect("read leaf DER bytes");

        // 3. Extract TBS from the issued leaf certificate
        let tbs_size = get_cert_size(&leaf_der_bytes[4..]).expect("valid TBS DER");
        let tbs_bytes = leaf_der_bytes[4..4 + tbs_size].to_vec();

        // 4. Endorse the TBS using parse_and_endorse_x509_cert with the given CaKey
        let endorsed_cert_bytes = parse_and_endorse_x509_cert(tbs_bytes, key)
            .expect("parse_and_endorse_x509_cert with ML-DSA seed should succeed");

        let mut mldsa_cert = EndorsedCert {
            format: CertFormat::X509,
            name: "mldsa_leaf_cert".to_string(),
            ignore_critical: true,
            bytes: endorsed_cert_bytes,
        };

        // 5. Validate that the newly signed ML-DSA leaf certificate validates against the CA PEM
        assert!(validate_cert_chain(ca_pem, &[mldsa_cert.clone()]).is_ok());

        // 6. Corrupt signature and verify validation fails
        let bad_byte = mldsa_cert.bytes.pop().unwrap() ^ 0xff;
        mldsa_cert.bytes.push(bad_byte);
        assert!(validate_cert_chain(ca_pem, &[mldsa_cert]).is_err());
    }

    #[test]
    fn validate_mldsa_signing() {
        let ca_pem = "./sw/device/silicon_creator/manuf/keys/fake/dice_mldsa_ca.pem";
        let ca_key = "./sw/device/silicon_creator/manuf/keys/fake/sk_mldsa.pkcs8.der";

        let key = CaKey::RawKey(RawKeyType::MldsaSeed(
            MlDsaSeed::read_pkcs8_der_file(ca_key).unwrap(),
        ));
        run_mldsa_ca_test(ca_pem, ca_key, &key);
    }

    #[test]
    fn validate_hsm_mldsa_signing() {
        let r = Runfiles::create().unwrap();
        let tokens_dir = rlocation!(r, "lowrisc_opentitan/signing/softhsm/tokens")
            .filter(|p| p.exists())
            .expect("signing/softhsm/tokens must exist in runfiles");

        let tmp_dir = tempfile::tempdir().unwrap();
        let tokens_dst = tmp_dir.path().join("tokens");
        opentitanlib::util::file::copy_dir_all(&tokens_dir, &tokens_dst).unwrap();

        let sandbox_conf = tmp_dir.path().join("softhsm2.conf");
        fs::write(
            &sandbox_conf,
            format!(
                "directories.tokendir = {}\nobjectstore.backend = file\nlog.level = WARNING\nslots.removable = false\n",
                tokens_dst.display()
            ),
        )
        .unwrap();

        // Configure environment variables for hsmtool
        // SAFETY: Single-threaded test setup configuring environment variables for the test process.
        unsafe {
            env::set_var("SOFTHSM2_CONF", &sandbox_conf);
            env::set_var("HSMTOOL_TOKEN", "fake_keys");
            env::set_var("HSMTOOL_PIN", "123456");
        }

        // Verify direct read_from_hsm_ef method
        let _ = MlDsaSeed::read_from_hsm_ef("fake_dice_mldsa_seed")
            .expect("MlDsaSeed::read_from_hsm_ef should succeed");

        let ca_pem = "./sw/device/silicon_creator/manuf/keys/fake/dice_mldsa_ca.pem";
        let ca_key = "./sw/device/silicon_creator/manuf/keys/fake/sk_mldsa.pkcs8.der";
        let key = CaKey::TokenKey(TokenKeyType::MldsaKey("fake_dice_mldsa_seed".to_string()));
        run_mldsa_ca_test(ca_pem, ca_key, &key);
    }
}
