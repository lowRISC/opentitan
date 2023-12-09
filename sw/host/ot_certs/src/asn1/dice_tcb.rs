// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use num_bigint_dig::BigUint;

use crate::asn1::builder::Builder;
use crate::asn1::x509::X509;
use crate::asn1::{Oid, Tag};
use crate::template::{FirmwareId, Flags, Value};

#[derive(Debug, Clone)]
pub struct DiceTcbInfo<'a> {
    pub vendor: &'a Option<Value<String>>,
    pub model: &'a Option<Value<String>>,
    pub version: &'a Option<Value<String>>,
    pub svn: &'a Option<Value<BigUint>>,
    pub layer: &'a Option<Value<BigUint>>,
    pub index: &'a Option<Value<BigUint>>,
    pub fwids: &'a Option<Vec<FirmwareId>>,
    pub flags: &'a Option<Flags>,
    pub vendor_info: &'a Option<Value<Vec<u8>>>,
    pub tcb_type: &'a Option<Value<Vec<u8>>>,
}

impl DiceTcbInfo<'_> {
    // From the DICE specification:
    // https://trustedcomputinggroup.org/wp-content/uploads/DICE-Attestation-Architecture-r23-final.pdf
    //
    // tcg OBJECT IDENTIFIER ::= {2 23 133}
    // tcg-dice OBJECT IDENTIFIER ::= { tcg platformClass(5) 4 }
    // tcg-dice-TcbInfo OBJECT IDENTIFIER ::= {tcg-dice 1}
    // DiceTcbInfo ::== SEQUENCE {
    //     vendor [0] IMPLICIT UTF8String OPTIONAL,
    //     model [1] IMPLICIT UTF8String OPTIONAL,
    //     version [2] IMPLICIT UTF8String OPTIONAL,
    //     svn [3] IMPLICIT INTEGER OPTIONAL,
    //     layer [4] IMPLICIT INTEGER OPTIONAL,
    //     index [5] IMPLICIT INTEGER OPTIONAL,
    //     fwids [6] IMPLICIT FWIDLIST OPTIONAL,
    //     flags [7] IMPLICIT OperationalFlags OPTIONAL,
    //     vendorInfo [8] IMPLICIT OCTET STRING OPTIONAL,
    //     type [9] IMPLICIT OCTET STRING OPTIONAL
    // }
    // FWIDLIST ::== SEQUENCE SIZE (1..MAX) OF FWID
    //     FWID ::== SEQUENCE {
    //     hashAlg OBJECT IDENTIFIER,
    //     digest OCTET STRING
    // }
    // OperationalFlags ::= BIT STRING {
    //     notConfigured (0),
    //     notSecure (1),
    //     recovery (2),
    //     debug (3)
    // }
    pub fn push_extension<B: Builder>(&self, builder: &mut B) -> Result<()> {
        X509::push_extension(builder, &Oid::DiceTcbInfo, false, |builder| {
            builder.push_seq(Some("dice_tcb_info".into()), |builder| {
                if let Some(vendor) = self.vendor {
                    builder.push_string(
                        Some("dice_vendor".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 0,
                        },
                        vendor,
                    )?;
                }
                if let Some(model) = self.model {
                    builder.push_string(
                        Some("dice_model".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 1,
                        },
                        model,
                    )?;
                }
                if let Some(version) = self.version {
                    builder.push_string(
                        Some("dice_version".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 2,
                        },
                        version,
                    )?;
                }
                if let Some(svn) = self.svn {
                    builder.push_integer(
                        Some("dice_svn".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 3,
                        },
                        svn,
                    )?;
                }
                if let Some(layer) = self.layer {
                    builder.push_integer(
                        Some("dice_layer".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 4,
                        },
                        layer,
                    )?;
                }
                if let Some(index) = self.index {
                    builder.push_integer(
                        Some("dice_index".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 5,
                        },
                        index,
                    )?;
                }
                if let Some(fwids) = self.fwids {
                    builder.push_tag(
                        Some("dice_fwids".into()),
                        &Tag::Context {
                            constructed: true,
                            value: 6,
                        },
                        |builder| {
                            for (idx, fwid) in fwids.iter().enumerate() {
                                builder.push_seq(Some("fwid".into()), |builder| {
                                    builder.push_oid(&fwid.hash_algorithm.oid())?;
                                    builder.push_octet_string(
                                        Some(format!("dice_fwids_{}", idx)),
                                        |builder| {
                                            builder.push_byte_array(
                                                Some(format!("dice_fwids_{}", idx)),
                                                &fwid.digest,
                                            )
                                        },
                                    )
                                })?;
                            }
                            Ok(())
                        },
                    )?;
                }
                if let Some(flags) = self.flags {
                    builder.push_bitstring(
                        Some("dice_flags".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 7,
                        },
                        &[
                            flags.not_configured.clone(),
                            flags.not_secure.clone(),
                            flags.recovery.clone(),
                            flags.debug.clone(),
                        ],
                    )?;
                }
                if let Some(vendor_info) = self.vendor_info {
                    builder.push_tag(
                        Some("dice_vendor_info".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 8,
                        },
                        |builder| {
                            builder.push_byte_array(Some("dice_vendor_info".into()), vendor_info)
                        },
                    )?;
                }
                if let Some(tcb_type) = self.tcb_type {
                    builder.push_tag(
                        Some("dice_type".into()),
                        &Tag::Context {
                            constructed: false,
                            value: 9,
                        },
                        |builder| builder.push_byte_array(Some("dice_type".into()), tcb_type),
                    )?;
                }
                Ok(())
            })
        })
    }
}
