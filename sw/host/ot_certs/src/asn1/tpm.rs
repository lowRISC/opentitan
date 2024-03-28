// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::asn1::builder::Builder;
use crate::asn1::x509::X509;
use crate::asn1::{Oid, Tag};
use crate::template::TpmExtension;

impl TpmExtension {
    // Fake TPM extension, just for example.
    //
    // fakeTpm OBJECT IDENTIFIER ::= {2 23 133 999}
    // TpmExt ::== SEQUENCE {
    //     value INTEGER,
    // }
    pub fn push_extension<B: Builder>(&self, builder: &mut B) -> Result<()> {
        X509::push_extension(builder, &Oid::TpmExt, false, |builder| {
            builder.push_seq(Some("tpm_ext".into()), |builder| {
                builder.push_integer(Some("tpm_value".into()), &Tag::Integer, &self.value)
            })
        })
    }
}
