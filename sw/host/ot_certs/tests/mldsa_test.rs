// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use ot_certs::codegen::generate_cert;
use ot_certs::template::Template;

const MLDSA_CERT: &str = include_str!("mldsa.hjson");

#[test]
fn test_mldsa_codegen() -> Result<()> {
    let tmpl = Template::from_hjson_str(MLDSA_CERT)?;
    let codegen = generate_cert("tests/mldsa.hjson", &tmpl)?;

    // Basic sanity checks on generated code.
    assert!(codegen.source_h.contains("mldsa_tbs_values_t"));
    assert!(codegen.source_h.contains("mldsa_sig_values_t"));
    assert!(codegen.source_h.contains("mldsa_build_tbs"));
    assert!(codegen.source_h.contains("mldsa_build_cert"));

    // Check that variables are present in the struct.
    assert!(codegen.source_h.contains("uint8_t *mldsa_pub_key;"));
    assert!(codegen.source_h.contains("uint8_t *mldsa_sig;"));

    Ok(())
}

#[test]
fn test_mldsa_random_test() -> Result<()> {
    let tmpl = Template::from_hjson_str(MLDSA_CERT)?;
    let random_data = tmpl.random_test()?;

    // Check that the generated random data has the correct variables.
    assert!(random_data.values.contains_key("mldsa_pub_key"));
    assert!(random_data.values.contains_key("mldsa_sig"));

    // Check sizes.
    if let Some(ot_certs::template::subst::SubstValue::ByteArray(bytes)) =
        random_data.values.get("mldsa_pub_key")
    {
        assert_eq!(bytes.len(), 1952);
    } else {
        panic!("mldsa_pub_key is not a ByteArray");
    }

    if let Some(ot_certs::template::subst::SubstValue::ByteArray(bytes)) =
        random_data.values.get("mldsa_sig")
    {
        assert_eq!(bytes.len(), 3300);
    } else {
        panic!("mldsa_sig is not a ByteArray");
    }

    Ok(())
}

#[test]
fn test_mldsa_invalid_pubkey_size() {
    let invalid_tmpl = r#"
    {
        name: "mldsa_invalid_pubkey",
        variables: {
            mldsa_pub_key: {
                type: "byte-array",
                exact-size: 1000, // Invalid size for ML-DSA-65 (expects 1952)
            },
            mldsa_sig: {
                type: "byte-array",
                exact-size: 3300,
            }
        },
        certificate: {
            serial_number: 1,
            issuer: [{ common_name: "Test" }],
            subject: [{ common_name: "Test" }],
            not_before: "20230101000000Z",
            not_after: "99991231235959Z",
            subject_public_key_info: {
                algorithm: "mldsa-65",
                public_key: { var: "mldsa_pub_key" },
            },
            signature: {
                algorithm: "mldsa-65",
                value: { var: "mldsa_sig" }
            }
        }
    }
    "#;
    let result = Template::from_hjson_str(invalid_tmpl);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(err.contains(
        "variable 'mldsa_pub_key' used in ML-DSA-65 public key must have exact-size 1952"
    ));
}

#[test]
fn test_mldsa_invalid_sig_size() {
    let invalid_tmpl = r#"
    {
        name: "mldsa_invalid_sig",
        variables: {
            mldsa_pub_key: {
                type: "byte-array",
                exact-size: 1952,
            },
            mldsa_sig: {
                type: "byte-array",
                exact-size: 3000, // Invalid size for ML-DSA-65 (expects 3300)
            }
        },
        certificate: {
            serial_number: 1,
            issuer: [{ common_name: "Test" }],
            subject: [{ common_name: "Test" }],
            not_before: "20230101000000Z",
            not_after: "99991231235959Z",
            subject_public_key_info: {
                algorithm: "mldsa-65",
                public_key: { var: "mldsa_pub_key" },
            },
            signature: {
                algorithm: "mldsa-65",
                value: { var: "mldsa_sig" }
            }
        }
    }
    "#;
    let result = Template::from_hjson_str(invalid_tmpl);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(
        err.contains("variable 'mldsa_sig' used in ML-DSA-65 signature must have exact-size 3300")
    );
}
