// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use ot_certs::codegen::generate_cert;
use ot_certs::template::Template;

const MLDSA_44_CERT: &str = include_str!("mldsa_44.hjson");
const MLDSA_65_CERT: &str = include_str!("mldsa_65.hjson");
const MLDSA_87_CERT: &str = include_str!("mldsa_87.hjson");

fn run_codegen_test(tmpl_str: &str, tmpl_path: &str, name: &str) -> Result<()> {
    let tmpl = Template::from_hjson_str(tmpl_str)?;
    let codegen = generate_cert(tmpl_path, &tmpl)?;

    // Basic sanity checks on generated code.
    assert!(codegen.source_h.contains(&format!("{}_tbs_values_t", name)));
    assert!(codegen.source_h.contains(&format!("{}_sig_values_t", name)));
    assert!(codegen.source_h.contains(&format!("{}_build_tbs", name)));
    assert!(codegen.source_h.contains(&format!("{}_build_cert", name)));

    // Check that variables are present in the struct.
    assert!(codegen.source_h.contains("uint8_t *mldsa_pub_key;"));
    assert!(codegen.source_h.contains("uint8_t *mldsa_sig;"));

    Ok(())
}

#[test]
fn test_mldsa_44_codegen() -> Result<()> {
    run_codegen_test(MLDSA_44_CERT, "tests/mldsa_44.hjson", "mldsa_44")
}

#[test]
fn test_mldsa_65_codegen() -> Result<()> {
    run_codegen_test(MLDSA_65_CERT, "tests/mldsa_65.hjson", "mldsa_65")
}

#[test]
fn test_mldsa_87_codegen() -> Result<()> {
    run_codegen_test(MLDSA_87_CERT, "tests/mldsa_87.hjson", "mldsa_87")
}

fn run_random_test(
    tmpl_str: &str,
    expected_pubkey_size: usize,
    expected_sig_size: usize,
) -> Result<()> {
    let tmpl = Template::from_hjson_str(tmpl_str)?;
    let random_data = tmpl.random_test()?;

    // Check that the generated random data has the correct variables.
    assert!(random_data.values.contains_key("mldsa_pub_key"));
    assert!(random_data.values.contains_key("mldsa_sig"));

    // Check sizes.
    if let Some(ot_certs::template::subst::SubstValue::ByteArray(bytes)) =
        random_data.values.get("mldsa_pub_key")
    {
        assert_eq!(bytes.len(), expected_pubkey_size);
    } else {
        panic!("mldsa_pub_key is not a ByteArray");
    }

    if let Some(ot_certs::template::subst::SubstValue::ByteArray(bytes)) =
        random_data.values.get("mldsa_sig")
    {
        assert_eq!(bytes.len(), expected_sig_size);
    } else {
        panic!("mldsa_sig is not a ByteArray");
    }

    Ok(())
}

#[test]
fn test_mldsa_44_random_test() -> Result<()> {
    run_random_test(MLDSA_44_CERT, 1312, 2420)
}

#[test]
fn test_mldsa_65_random_test() -> Result<()> {
    run_random_test(MLDSA_65_CERT, 1952, 3300)
}

#[test]
fn test_mldsa_87_random_test() -> Result<()> {
    run_random_test(MLDSA_87_CERT, 2592, 4627)
}

fn run_invalid_pubkey_size_test(
    algorithm: &str,
    correct_pubkey_size: usize,
    incorrect_pubkey_size: usize,
    correct_sig_size: usize,
    algo_name_in_err: &str,
) {
    let invalid_tmpl = format!(
        r#"
    {{
        name: "mldsa_invalid_pubkey",
        variables: {{
            mldsa_pub_key: {{
                type: "byte-array",
                exact-size: {incorrect_pubkey_size},
            }},
            mldsa_sig: {{
                type: "byte-array",
                exact-size: {correct_sig_size},
            }}
        }},
        certificate: {{
            serial_number: 1,
            issuer: [{{ common_name: "Test" }}],
            subject: [{{ common_name: "Test" }}],
            not_before: "20230101000000Z",
            not_after: "99991231235959Z",
            subject_public_key_info: {{
                algorithm: "{algorithm}",
                public_key: {{ var: "mldsa_pub_key" }},
            }},
            signature: {{
                algorithm: "{algorithm}",
                value: {{ var: "mldsa_sig" }}
            }}
        }}
    }}
    "#
    );
    let result = Template::from_hjson_str(&invalid_tmpl);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(err.contains(&format!(
        "variable 'mldsa_pub_key' used in {} public key must have exact-size {}",
        algo_name_in_err, correct_pubkey_size
    )));
}

#[test]
fn test_mldsa_44_invalid_pubkey_size() {
    run_invalid_pubkey_size_test("mldsa-44", 1312, 1000, 2420, "ML-DSA-44");
}

#[test]
fn test_mldsa_65_invalid_pubkey_size() {
    run_invalid_pubkey_size_test("mldsa-65", 1952, 1000, 3300, "ML-DSA-65");
}

#[test]
fn test_mldsa_87_invalid_pubkey_size() {
    run_invalid_pubkey_size_test("mldsa-87", 2592, 1000, 4627, "ML-DSA-87");
}

fn run_invalid_sig_size_test(
    algorithm: &str,
    correct_pubkey_size: usize,
    correct_sig_size: usize,
    incorrect_sig_size: usize,
    algo_name_in_err: &str,
) {
    let invalid_tmpl = format!(
        r#"
    {{
        name: "mldsa_invalid_sig",
        variables: {{
            mldsa_pub_key: {{
                type: "byte-array",
                exact-size: {correct_pubkey_size},
            }},
            mldsa_sig: {{
                type: "byte-array",
                exact-size: {incorrect_sig_size},
            }}
        }},
        certificate: {{
            serial_number: 1,
            issuer: [{{ common_name: "Test" }}],
            subject: [{{ common_name: "Test" }}],
            not_before: "20230101000000Z",
            not_after: "99991231235959Z",
            subject_public_key_info: {{
                algorithm: "{algorithm}",
                public_key: {{ var: "mldsa_pub_key" }},
            }},
            signature: {{
                algorithm: "{algorithm}",
                value: {{ var: "mldsa_sig" }}
            }}
        }}
    }}
    "#
    );
    let result = Template::from_hjson_str(&invalid_tmpl);
    assert!(result.is_err());
    let err = result.unwrap_err().to_string();
    assert!(err.contains(&format!(
        "variable 'mldsa_sig' used in {} signature must have exact-size {}",
        algo_name_in_err, correct_sig_size
    )));
}

#[test]
fn test_mldsa_44_invalid_sig_size() {
    run_invalid_sig_size_test("mldsa-44", 1312, 2420, 3000, "ML-DSA-44");
}

#[test]
fn test_mldsa_65_invalid_sig_size() {
    run_invalid_sig_size_test("mldsa-65", 1952, 3300, 3000, "ML-DSA-65");
}

#[test]
fn test_mldsa_87_invalid_sig_size() {
    run_invalid_sig_size_test("mldsa-87", 2592, 4627, 3000, "ML-DSA-87");
}
