// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use base64ct::Encoding;

use ot_certs::asn1::der::Der;
use ot_certs::template::subst::{Subst, SubstData};
use ot_certs::template::{RawOr, Template};

const GENERIC_CERT: &str = include_str!("generic.hjson");
const EXAMPLE_DATA: &str = include_str!("example_data.json");
const EXAMPLE_CERT: &str = include_str!("example.hjson");

const GENERIC_FW_IDS_RAW: &str = include_str!("generic_fw_ids_raw.hjson");
const EXAMPLE_FW_IDS_RAW_DATA: &str = include_str!("example_fw_ids_raw_data.json");
const GENERIC_RAW_EXTS: &str = include_str!("generic_raw_exts.hjson");

#[test]
fn subst_generic() -> Result<()> {
    // Parse generic certificate.
    let generic_tmpl =
        Template::from_hjson_str(GENERIC_CERT).expect("failed to parse generic template");
    // Parse example certificate.
    let example_tmpl =
        Template::from_hjson_str(EXAMPLE_CERT).expect("failed to parse example template");
    // Load data.
    let test_data = SubstData::from_json(EXAMPLE_DATA).expect("failed to parse example data");
    // Substitute data into the template.
    let mut cert = generic_tmpl.subst(&test_data)?;
    // We need to change the name to make sure that it matches.
    cert.name = "example".to_string();
    // Check that we obtain the example certificate template.
    if example_tmpl != cert {
        println!("expected: {:#?}", example_tmpl);
        println!("got: {cert:#?}");
        bail!(
            "example.hjson does not correspond to substituting example_data.json in generic.hjson"
        );
    }

    Ok(())
}

#[test]
fn subst_fw_ids_raw() -> Result<()> {
    let generic_tmpl =
        Template::from_hjson_str(GENERIC_CERT).expect("failed to parse generic template");
    let test_data = SubstData::from_json(EXAMPLE_DATA).expect("failed to parse example data");
    let mut cert_normal = generic_tmpl.subst(&test_data)?;
    cert_normal.name = "example".to_string();

    let generic_raw_tmpl =
        Template::from_hjson_str(GENERIC_FW_IDS_RAW).expect("failed to parse generic raw template");
    let test_raw_data =
        SubstData::from_json(EXAMPLE_FW_IDS_RAW_DATA).expect("failed to parse example raw data");
    let mut cert_raw = generic_raw_tmpl.subst(&test_raw_data)?;
    cert_raw.name = "example".to_string();

    let cert_normal_der = ot_certs::x509::generate_certificate(&cert_normal)?;
    let cert_raw_der = ot_certs::x509::generate_certificate(&cert_raw)?;

    if cert_normal_der != cert_raw_der {
        bail!("re-serialized cert DER does not match pre-serialized cert DER");
    }

    Ok(())
}

#[test]
fn subst_private_extensions_raw() -> Result<()> {
    let generic_tmpl =
        Template::from_hjson_str(GENERIC_CERT).expect("failed to parse generic template");
    let test_data = SubstData::from_json(EXAMPLE_DATA).expect("failed to parse example data");
    let cert_normal = generic_tmpl.subst(&test_data)?;

    let exts = match &cert_normal.certificate().unwrap().private_extensions {
        RawOr::Type(exts) => exts.clone(),
        RawOr::Raw(_) => bail!("expected structured extensions in cert_normal"),
    };
    let ext_bytes = Der::generate(|builder| {
        for ext in &exts {
            ot_certs::asn1::x509::X509::push_cert_extension(builder, ext)?
        }
        Ok(())
    })?;

    let generic_raw_tmpl = Template::from_hjson_str(GENERIC_RAW_EXTS)
        .expect("failed to parse generic raw exts template");

    let mut test_raw_data = SubstData::from_json(EXAMPLE_DATA)?;
    test_raw_data.values.insert(
        "raw_private_extensions".to_string(),
        ot_certs::template::subst::SubstValue::ByteArray(ext_bytes),
    );

    let mut cert_raw = generic_raw_tmpl.subst(&test_raw_data)?;
    cert_raw.name = "example".to_string();

    let cert_normal_der = ot_certs::x509::generate_certificate(&cert_normal)?;
    let cert_raw_der = ot_certs::x509::generate_certificate(&cert_raw)?;

    if cert_normal_der != cert_raw_der {
        println!("cert_normal_der len: {}", cert_normal_der.len());
        println!("cert_raw_der len:    {}", cert_raw_der.len());
        println!(
            "cert_normal_der: {}",
            base64ct::Base64::encode_string(&cert_normal_der)
        );
        println!(
            "cert_raw_der:    {}",
            base64ct::Base64::encode_string(&cert_raw_der)
        );
        bail!("re-serialized cert DER with raw exts does not match normal cert DER");
    }

    Ok(())
}
