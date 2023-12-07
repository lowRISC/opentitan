// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod builder;
pub mod der;

/// An ASN1 tag.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Tag {
    // Universal tags.
    Boolean,
    BitString,
    GeneralizedTime,
    Integer,
    OctetString,
    Oid,
    PrintableString,
    Sequence,
    Set,
    Utf8String,
    /// Context tags.
    Context {
        constructed: bool,
        value: usize,
    },
}

/// An ASN1 object identifier.
#[derive(Debug, Clone, PartialEq, Eq, strum::Display)]
pub enum Oid {
    // Custom oid.
    Custom(String),
}

impl Oid {
    /// Return the standard notation of the OID as string.
    pub fn oid(&self) -> &str {
        match self {
            Oid::Custom(oid) => oid,
        }
    }
}
