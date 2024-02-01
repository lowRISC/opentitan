// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};

use ot_certs::template::subst::{Subst, SubstData};
use ot_certs::template::Template;

const GENERIC_CERT: &str = include_str!("generic.hjson");
const EXAMPLE_DATA: &str = include_str!("example_data.json");
const EXAMPLE_CERT: &str = include_str!("example.hjson");

#[test]
fn main() -> Result<()> {
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
