// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};

use ot_certs::template::Template;
use ot_certs::template::subst::Subst;
use ot_certs::x509;

const EXTENSIONS_TEMPLATE: &str = include_str!("extensions.hjson");

#[test]
fn main() -> Result<()> {
    // Parse extensions template.
    let tmpl =
        Template::from_hjson_str(EXTENSIONS_TEMPLATE).expect("failed to parse extensions template");

    // Check certificate is None.
    if tmpl.certificate().is_ok() {
        bail!("expected certificate to be None");
    }

    // Generate some random test data.
    let test_data = tmpl.random_test()?;
    println!("test data: {test_data:?}");

    // Substitute data into the template.
    let cert = tmpl.subst(&test_data)?;

    // Generating private extensions should succeed.
    let ext_bytes = x509::generate_private_extensions(&cert)?;
    println!("Generated extensions size: {}", ext_bytes.len());

    // Generating full certificate should fail.
    let cert_res = x509::generate_certificate(&cert);
    if cert_res.is_ok() {
        bail!("expected generate_certificate to fail on extension-only template");
    }

    Ok(())
}
