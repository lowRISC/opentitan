// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use base64ct::Encoding;
use num_bigint_dig::BigUint;
use num_traits::cast::FromPrimitive;
use num_traits::Num;

use ot_certs::asn1::der::Der;
use ot_certs::template::{
    DiceTcbInfoExtension, DiceTcbInfoFlags, FirmwareId, HashAlgorithm, Value,
};
use ot_certs::x509::extension::parse_dice_tcb_info_extension;

fn check_dice_tcb_info(dice_tcb_info: DiceTcbInfoExtension) -> Result<()> {
    // Generate the DER for this DICE TCB Info.
    let der = Der::generate(|builder| dice_tcb_info.push_extension_raw(builder))?;
    // Parse DER back.
    let parsed_tcb =
        parse_dice_tcb_info_extension(&der).context("could not parse DICE TCB Info der")?;
    // Check that it matches the original one.
    if parsed_tcb != dice_tcb_info {
        println!("expected: {dice_tcb_info:#?}");
        println!("got: {parsed_tcb:#?}");
        println!("DER: {}", base64ct::Base64::encode_string(&der));
        bail!("parsed DICE TCB does not match the expected one");
    }
    Ok(())
}

#[test]
fn main() -> Result<()> {
    // For each optional field, we exercise one case where it is set
    // and one case where it is not set.
    check_dice_tcb_info(DiceTcbInfoExtension {
        model: Some(Value::Literal("Model".into())),
        vendor: None,
        version: Some(Value::Literal("Version".into())),
        svn: None,
        layer: Some(Value::Literal(BigUint::from_u32(42).unwrap())),
        fw_ids: None,
        flags: Some(DiceTcbInfoFlags {
            not_configured: Value::Literal(true),
            not_secure: Value::Literal(true),
            recovery: Value::Literal(false),
            debug: Value::Literal(true),
        }),
    })?;

    check_dice_tcb_info(DiceTcbInfoExtension {
        model: None,
        vendor: Some(Value::Literal("Vendor".into())),
        version: None,
        svn: Some(Value::Literal(BigUint::from_str_radix(
            "89485897489778474678876487678657",
            10,
        )?)),
        layer: None,
        fw_ids: Some(vec![
            FirmwareId {
                hash_algorithm: HashAlgorithm::Sha256,
                digest: Value::Literal(vec![
                    0x46, 0x56, 0x44, 0xd9, 0x35, 0x38, 0x57, 0x83, 0x65, 0x83, 0x57, 0x58, 0x37,
                    0x58, 0xc5, 0x93, 0x58, 0x3b, 0x65, 0x37,
                ]),
            },
            FirmwareId {
                hash_algorithm: HashAlgorithm::Sha256,
                digest: Value::Literal(vec![
                    0x00, 0x9e, 0x98, 0x09, 0xf8, 0x59, 0x78, 0x32, 0x75, 0x92, 0x85, 0x7a, 0x09,
                    0x3f, 0x53, 0x90, 0x78, 0x62, 0x65, 0x89,
                ]),
            },
        ]),
        flags: None,
    })?;

    Ok(())
}
