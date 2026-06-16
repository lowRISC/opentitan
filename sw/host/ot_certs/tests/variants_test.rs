// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use ot_certs::codegen::generate_cert;
use ot_certs::template::Template;
use ot_certs::template::subst::Subst;

const VARIANTS_CERT: &str = include_str!("variants.hjson");

#[test]
fn test_variants_codegen() -> Result<()> {
    let tmpl = Template::from_hjson_str(VARIANTS_CERT)?;
    let codegen = generate_cert("tests/variants.hjson", &tmpl)?;

    // Basic sanity checks on generated code.
    assert!(codegen.source_h.contains("variants_tbs_values_t"));
    assert!(codegen.source_h.contains("variants_sig_values_t"));
    assert!(codegen.source_h.contains("variants_build_tbs"));
    assert!(codegen.source_h.contains("variants_build_cert"));

    // Check that variables are present in the struct.
    assert!(codegen.source_h.contains("uint32_t pub_key_type;"));
    assert!(codegen.source_h.contains("uint32_t sig_type;"));
    assert!(codegen.source_h.contains("uint8_t *pub_key_ec_x;"));
    assert!(codegen.source_h.contains("uint8_t *pub_key_mldsa_87;"));
    assert!(codegen.source_h.contains("uint8_t *pub_key_mldsa_44;"));
    assert!(codegen.source_h.contains("uint8_t *sig_mldsa_87;"));
    assert!(codegen.source_h.contains("uint8_t *sig_mldsa_44;"));

    // Check that skip helpers are generated.
    assert!(codegen.source_c.contains("template_skip_const(&state,"));

    Ok(())
}

#[test]
fn test_variants_random_test() -> Result<()> {
    let tmpl = Template::from_hjson_str(VARIANTS_CERT)?;
    for i in 0..10 {
        let random_data = tmpl.random_test()?;
        eprintln!("Run {}: random_data = {:#?}", i, random_data);
        // Verify substitution succeeds.
        let subst_tmpl = tmpl.subst(&random_data)?;
        eprintln!("Run {}: subst_tmpl = {:#?}", i, subst_tmpl);
        // Verify DER generation succeeds.
        let _cert = ot_certs::x509::generate_certificate(&subst_tmpl)?;
    }
    Ok(())
}
