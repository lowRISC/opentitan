// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};

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

    /// Return the DER encoding of the OID as a list of bytes.
    pub fn to_der(&self) -> Result<Vec<u8>> {
        let mut components = self
            .oid()
            .split('.')
            .map(|s| {
                s.parse::<u32>()
                    .with_context(|| format!("invalid OID component '{s}'"))
            })
            .collect::<Result<Vec<_>>>()?;
        // From X.690 spec, section 8.19:
        // The number of subidentifiers (N) shall be one less than the number of object identifier components
        // in the object identifier value being encoded. The numerical value of the first subidentifier is derived
        // from the values of the first two object identifier components in the object identifier value being encoded,
        // using the formula: (X*40) + Y where X is the value of the first object identifier component and Y is the value
        // of the second object identifier component.
        components.reverse();
        let first = components
            .pop()
            .context("cannot call push_oid with an empty OID")?;
        let second = components
            .pop()
            .context("cannot call push_oid with a single-component OID")?;
        components.push(40 * first + second);
        components.reverse();
        let mut bytes = Vec::<u8>::new();
        for comp in components {
            // The contents octets shall be an (ordered) list of encodings of subidentifiers (see 8.19.3 and 8.19.4) concatenated
            // together. Each subidentifier is represented as a series of (one or more) octets. Bit 8 of each octet indicates whether it is the last in the
            // series: bit 8 of the last octet is zero; bit 8 of each preceding octet is one. Bits 7 to 1 of the octets in the series collectively
            // encode the subidentifier. Conceptually, these groups of bits are concatenated to form an unsigned binary number whose most
            // significant bit is bit 7 of the first octet and whose least significant bit is bit 1 of the last octet. The subidentifier shall be
            // encoded in the fewest possible octets, that is, the leading octet of the subidentifier shall not have the value 8016

            // Compute the length that we need: each byte stores 7 bits so this is the
            // the log in base 128 of the number.
            let mut copy_comp = comp;
            let mut length = 0;
            while copy_comp > 0 {
                length += 1;
                copy_comp >>= 7;
            }
            if length == 0 {
                length = 1;
            }
            // Create the bytes
            for i in (0..length).rev() {
                // Extract 7-bit chunk of the number.
                let mut byte = ((comp >> (7 * i)) & 0x7f) as u8;
                // Add continuation marker.
                if i != 0 {
                    byte |= 0x80;
                }
                bytes.push(byte);
            }
        }
        Ok(bytes)
    }
}
