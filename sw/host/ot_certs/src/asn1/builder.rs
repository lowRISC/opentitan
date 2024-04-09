// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module provides a trait to abstract the generation of an ASN1
//! document. The particularity of this trait is that the base values
//! are of type `Value<T>` which can either be literals or variables.

use anyhow::{ensure, Result};
use num_bigint_dig::BigUint;

use crate::asn1::{Oid, Tag};
use crate::template::Value;

/// Helper function to add a suffix to a name hint.
pub fn concat_suffix(name_hint: &Option<String>, suffix: &str) -> Option<String> {
    name_hint.as_ref().map(|s| format!("{}_{}", s, suffix))
}

/// Trait for an abstract ASN1 builder.
///
/// This builder does not specify what the output is, but only provides
/// basic functions to build an ASN1 document. A possible implementation
/// would be to output bytes to produce an actual DER encoding for example.
/// This can also be used to generate C code that calls into a C library to
/// produce a certificate. For this reason, this builder does not provide any
/// way to access the result, as this is implementation specific.
pub trait Builder {
    /// Push a byte into the ASN1 output.
    fn push_byte(&mut self, val: u8) -> Result<()>;

    /// Push a tagged boolean into the ASN1 output.
    fn push_boolean(&mut self, tag: &Tag, val: &Value<bool>) -> Result<()>;

    /// Push a tagged integer into the ASN1 output. The name hint can be used by
    /// the implementation for documentation purpose, or completely ignored.
    fn push_integer(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        val: &Value<BigUint>,
    ) -> Result<()>;

    /// Push a byte array into the ASN1 output, representing an integer. If the provided
    /// buffer is smaller than the provided size, it will be padded with zeroes. Note that this
    /// function does not add a tag to the ASN1 output.
    fn push_integer_pad(
        &mut self,
        name_hint: Option<String>,
        val: &Value<BigUint>,
        size: usize,
    ) -> Result<()>;

    /// Push a byte array of fixed length into the ASN1 output. Note that this function does not add a tag to
    /// the ASN1 output.
    fn push_byte_array(&mut self, name_hint: Option<String>, val: &Value<Vec<u8>>) -> Result<()>;

    /// Push a tagged string into the ASN1 output.
    fn push_string(
        &mut self,
        name_hint: Option<String>,
        str_type: &Tag,
        val: &Value<String>,
    ) -> Result<()>;

    /// Push a tagged object identifier into the ASN1 output.
    fn push_oid(&mut self, oid: &Oid) -> Result<()>;

    /// Push tagged content into the ASN1 output. The closure can use any available function of the builder
    /// and produces the content of the tagged data.
    fn push_tag(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()>;

    /// Push a tagged octet string into the ASN1 output. The closure can use any available function of the builder
    /// and produces the content of the octet string.
    fn push_octet_string(
        &mut self,
        name_hint: Option<String>,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.push_tag(name_hint, &Tag::OctetString, |builder| gen(builder))
    }

    /// Push a sequence into the ASN1 output. The closure can use any available function of the builder
    /// and produces the content of the sequence.
    fn push_seq(
        &mut self,
        name_hint: Option<String>,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.push_tag(name_hint, &Tag::Sequence, gen)
    }

    /// Push a sequence into the ASN1 output. The closure can use any available function of the builder
    /// and produces the content of the set.
    fn push_set(
        &mut self,
        name_hint: Option<String>,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.push_tag(name_hint, &Tag::Set, gen)
    }

    /// Push tagged content into the ASN1 output as a bitstring. The closure can use any available function of the builder
    /// and the resulting content will be stored as a BITSTRING using the provided tag and unused number of bits.
    fn push_as_bit_string(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        unused_bits: usize,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.push_tag(name_hint, tag, |builder| {
            ensure!(
                unused_bits <= 7,
                "unused bits value must be in the range 0 to 7"
            );
            builder.push_byte(unused_bits as u8)?;
            gen(builder)
        })
    }

    // Push a tagged constant bit string into the ASN1 output.
    fn push_bitstring(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        bits: &[Value<bool>],
    ) -> Result<()>;
}
