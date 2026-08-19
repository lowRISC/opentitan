// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use core::include_bytes;

use ot_certs::asn1::{der, x509};
use ot_certs::template::Template;
use ot_certs::template::subst::{Subst, SubstData};
use ot_certs::x509::generate_certificate;

const UDS_CERT_TEMPLATE: &str =
    include_str!("../../../../sw/device/silicon_creator/lib/cert/uds.hjson");
const GOLDEN_ECDSA_TBS_INPUT_DATA: &str = include_str!("uds_ecdsa_tbs_input_golden.json");
const GOLDEN_ECDSA_TBS_OUTPUT_DATA: &[u8] = include_bytes!("uds_ecdsa_tbs_golden.der");
const GOLDEN_ECDSA_ENDORSED_CERT_INPUT_DATA: &str =
    include_str!("uds_ecdsa_endorsed_cert_input_golden.json");
const GOLDEN_ECDSA_ENDORSED_CERT_OUTPUT_DATA: &[u8] =
    include_bytes!("uds_ecdsa_endorsed_cert_golden.der");

const GOLDEN_MLDSA44_TBS_INPUT_DATA: &str = include_str!("uds_mldsa44_tbs_input_golden.json");
const GOLDEN_MLDSA44_TBS_OUTPUT_DATA: &[u8] = include_bytes!("uds_mldsa44_tbs_golden.der");
const GOLDEN_MLDSA44_ENDORSED_CERT_INPUT_DATA: &str =
    include_str!("uds_mldsa44_endorsed_cert_input_golden.json");
const GOLDEN_MLDSA44_ENDORSED_CERT_OUTPUT_DATA: &[u8] =
    include_bytes!("uds_mldsa44_endorsed_cert_golden.der");

const GOLDEN_MLDSA87_TBS_INPUT_DATA: &str = include_str!("uds_mldsa87_tbs_input_golden.json");
const GOLDEN_MLDSA87_TBS_OUTPUT_DATA: &[u8] = include_bytes!("uds_mldsa87_tbs_golden.der");
const GOLDEN_MLDSA87_ENDORSED_CERT_INPUT_DATA: &str =
    include_str!("uds_mldsa87_endorsed_cert_input_golden.json");
const GOLDEN_MLDSA87_ENDORSED_CERT_OUTPUT_DATA: &[u8] =
    include_bytes!("uds_mldsa87_endorsed_cert_golden.der");

#[test]
fn compare_uds_ecdsa_tbs() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let ecdsa_test_data = SubstData::from_json(GOLDEN_ECDSA_TBS_INPUT_DATA)
        .expect("Golden data for ECDSA must be parseable as JSON");
    let subst_template = uds_template
        .subst(&ecdsa_test_data)
        .expect("Template substitution for UDS ECDSA TBS must succeed");
    let tbs = der::Der::generate(|builder| {
        x509::X509::push_tbs_certificate(builder, &subst_template.certificate)
    })
    .expect("TBS UDS certificate generation to succeed");

    assert_eq!(tbs, GOLDEN_ECDSA_TBS_OUTPUT_DATA);
}

#[test]
fn compare_uds_ecdsa_endorsed_cert() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let ecdsa_test_data = SubstData::from_json(GOLDEN_ECDSA_ENDORSED_CERT_INPUT_DATA)
        .expect("Golden data for ECDSA must be parseable as JSON");
    let subst_template = uds_template
        .subst(&ecdsa_test_data)
        .expect("Template substitution for UDS ECDSA endorsed certificate must succeed");
    let endorsed_cert = generate_certificate(&subst_template)
        .expect("Certificate generation for UDS ECDSA certificate must succeed");

    assert_eq!(endorsed_cert, GOLDEN_ECDSA_ENDORSED_CERT_OUTPUT_DATA);
}

#[test]
fn compare_uds_mldsa44_tbs() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let mldsa_test_data = SubstData::from_json(GOLDEN_MLDSA44_TBS_INPUT_DATA)
        .expect("Golden data for MLDSA44 must be parseable as JSON");
    let subst_template = uds_template
        .subst(&mldsa_test_data)
        .expect("Template substitution for UDS MLDSA44 TBS must succeed");
    let tbs = der::Der::generate(|builder| {
        x509::X509::push_tbs_certificate(builder, &subst_template.certificate)
    })
    .expect("TBS UDS certificate generation to succeed");

    assert_eq!(tbs, GOLDEN_MLDSA44_TBS_OUTPUT_DATA);
}

#[test]
fn compare_uds_mldsa44_endorsed_cert() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let ecdsa_test_data = SubstData::from_json(GOLDEN_MLDSA44_ENDORSED_CERT_INPUT_DATA)
        .expect("Golden data for MLDSA44 must be parseable as JSON");
    let subst_template = uds_template
        .subst(&ecdsa_test_data)
        .expect("Template substitution for UDS MLDSA44 endorsed certificate must succeed");
    let endorsed_cert = generate_certificate(&subst_template)
        .expect("Certificate generation for UDS MLDSA44 certificate must succeed");

    assert_eq!(endorsed_cert, GOLDEN_MLDSA44_ENDORSED_CERT_OUTPUT_DATA);
}

#[test]
fn compare_uds_mldsa87_tbs() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let mldsa_test_data = SubstData::from_json(GOLDEN_MLDSA87_TBS_INPUT_DATA)
        .expect("Golden data for MLDSA87 must be parseable as JSON");
    let subst_template = uds_template
        .subst(&mldsa_test_data)
        .expect("Template substitution for UDS MLDSA87 TBS must succeed");
    let tbs = der::Der::generate(|builder| {
        x509::X509::push_tbs_certificate(builder, &subst_template.certificate)
    })
    .expect("TBS UDS certificate generation to succeed");

    assert_eq!(tbs, GOLDEN_MLDSA87_TBS_OUTPUT_DATA);
}

#[test]
fn compare_uds_mldsa87_endorsed_cert() {
    let uds_template = Template::from_hjson_str(UDS_CERT_TEMPLATE)
        .expect("UDS certificate template must be parseable as HJSON");
    let ecdsa_test_data = SubstData::from_json(GOLDEN_MLDSA87_ENDORSED_CERT_INPUT_DATA)
        .expect("Golden data for MLDSA87 must be parseable as JSON");
    let subst_template = uds_template
        .subst(&ecdsa_test_data)
        .expect("Template substitution for UDS MLDSA87 endorsed certificate must succeed");
    let endorsed_cert = generate_certificate(&subst_template)
        .expect("Certificate generation for UDS MLDSA87 certificate must succeed");

    assert_eq!(endorsed_cert, GOLDEN_MLDSA87_ENDORSED_CERT_OUTPUT_DATA);
}
