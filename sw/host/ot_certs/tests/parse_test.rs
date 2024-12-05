// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use base64ct::Encoding;

use ot_certs::template::subst::Subst;
use ot_certs::template::Template;
use ot_certs::x509;

const GENERIC_CERT: &str = include_str!("generic.hjson");

#[test]
fn main() -> Result<()> {
    // Parse generic certificate.
    let generic_tmpl =
        Template::from_hjson_str(GENERIC_CERT).expect("failed to parse generic template");
    // Generate some random test data.
    let test_data = generic_tmpl.random_test()?;
    // Print test data so we can reproduce the test on failure.
    println!("test data: {test_data:?}");
    // Substitute data into the template.
    let cert = generic_tmpl.subst(&test_data)?;
    // Use DER to generate a binary certificate.
    let der_cert = x509::generate_certificate(&cert)?;
    // Use openssl to parse the binary certificate.
    let parsed_cert = x509::parse_certificate(&der_cert)?;
    // Check that this is exactly what we started with.
    println!("expected: {:#?}", cert.certificate);
    println!("got: {parsed_cert:#?}");
    println!("DER: {}", base64ct::Base64::encode_string(&der_cert));
    if cert.certificate != parsed_cert {
        bail!("parsed certificate does not match the expected one")
    }

    Ok(())
}
