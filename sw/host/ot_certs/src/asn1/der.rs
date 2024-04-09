// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module provides an implementation of the `Builder` trait to produce
//! a DER output. This module only supports literal values for variables
//! since it needs to know the concrete values to produce the output.

use anyhow::{bail, ensure, Result};
use num_bigint_dig::BigUint;

use crate::asn1::builder::Builder;
use crate::asn1::{Oid, Tag};
use crate::template::{Value, Variable};

impl Tag {
    // Return the DER representation of the identifier octet(s) of a tag.
    pub fn to_der(&self) -> Result<Vec<u8>> {
        const ASN1_TAG_CLASS_CONTEXT: u8 = 2 << 6;
        const ASN1_TAG_FORM_PRIMITIVE: u8 = 0 << 5;
        const ASN1_TAG_FORM_CONSTRUCTED: u8 = 1 << 5;
        // The class and numbers of tags are defined in X.680 in textual
        // form (https://www.itu.int/rec/T-REC-X.680). See section 18 and
        // onwards.
        let tag = match self {
            Tag::Boolean => 0x01,
            Tag::BitString => 0x03,
            Tag::GeneralizedTime => 0x018,
            Tag::Integer => 0x02,
            Tag::OctetString => 0x04,
            Tag::Oid => 0x06,
            Tag::PrintableString => 0x13,
            Tag::Sequence => 0x30,
            Tag::Set => 0x31,
            Tag::Utf8String => 0x0c,
            &Tag::Context { constructed, value } => {
                // Only support small numbers for now.
                ensure!(value <= 30, "tag number above 30 are not supported for now");
                let constructed = if constructed {
                    ASN1_TAG_FORM_CONSTRUCTED
                } else {
                    ASN1_TAG_FORM_PRIMITIVE
                };
                ASN1_TAG_CLASS_CONTEXT | constructed | (value as u8)
            }
        };
        Ok(vec![tag])
    }
}

pub struct Der {
    output: Vec<u8>,
}

impl Der {
    fn new() -> Der {
        Der { output: Vec::new() }
    }

    pub fn generate(gen: impl FnOnce(&mut Self) -> Result<()>) -> Result<Vec<u8>> {
        let mut der = Der::new();
        gen(&mut der)?;
        Ok(der.output)
    }

    fn get_value_or_error<T>(val: &Value<T>) -> Result<&T> {
        match val {
            Value::Literal(x) => Ok(x),
            Value::Variable(Variable { name, .. }) => bail!(
                "cannot push value of variable {name}: the DER generator does not support variables"
            ),
        }
    }

    /// Push a byte into the ASN1 output.
    fn push_bytes(&mut self, val: &[u8]) -> Result<()> {
        self.output.extend(val);
        Ok(())
    }
}

impl Builder for Der {
    /// Push a byte into the ASN1 output.
    fn push_byte(&mut self, val: u8) -> Result<()> {
        self.output.push(val);
        Ok(())
    }

    /// Push a tagged boolean into the ASN1 output.
    fn push_boolean(&mut self, tag: &Tag, val: &Value<bool>) -> Result<()> {
        let val = Self::get_value_or_error(val)?;
        let val = if *val { 0xffu8 } else { 0x00u8 };
        self.push_tag(None, tag, |builder| builder.push_byte(val))
    }

    /// Push a tagged integer into the ASN1 output. The name hint can be used by
    /// the implementation for documentation purpose, or completely ignored.
    fn push_integer(
        &mut self,
        _name_hint: Option<String>,
        tag: &Tag,
        val: &Value<BigUint>,
    ) -> Result<()> {
        let mut bytes = Self::get_value_or_error(val)?.to_bytes_be();
        // DER integers are always in two's complement so if the MSB of the MSB byte is set,
        // we need add a 0 byte to make sure it is not mistaken for a negative integer.
        if (bytes[0] >> 7) == 1 {
            bytes.insert(0, 0x00);
        }
        let val = Value::Literal(bytes);
        self.push_tag(None, tag, |builder| builder.push_byte_array(None, &val))
    }

    /// Push a byte array into the ASN1 output, representing an integer. If the provided
    /// buffer is smaller than the provided size, it will be padded with zeroes. Note that this
    /// function does not add a tag to the ASN1 output.
    fn push_integer_pad(
        &mut self,
        _name_hint: Option<String>,
        val: &Value<BigUint>,
        size: usize,
    ) -> Result<()> {
        let val = Self::get_value_or_error(val)?;
        let mut bytes = val.to_bytes_be();
        while bytes.len() < size {
            bytes.insert(0, 0x0);
        }
        let val = Value::Literal(bytes);
        self.push_byte_array(None, &val)
    }

    /// Push a byte array of fixed length into the ASN1 output. Note that this function does not add a tag to
    /// the ASN1 output.
    fn push_byte_array(&mut self, _name_hint: Option<String>, val: &Value<Vec<u8>>) -> Result<()> {
        let val = Self::get_value_or_error(val)?;
        self.output.extend(val);
        Ok(())
    }

    /// Push a tagged string into the ASN1 output.
    fn push_string(
        &mut self,
        _name_hint: Option<String>,
        str_type: &Tag,
        val: &Value<String>,
    ) -> Result<()> {
        let val = Self::get_value_or_error(val)?;
        let val = Value::Literal(val.as_bytes().to_vec());
        self.push_tag(None, str_type, |builder| {
            builder.push_byte_array(None, &val)
        })
    }

    /// Push a tagged object identifier into the ASN1 output.
    fn push_oid(&mut self, oid: &Oid) -> Result<()> {
        let val = Value::Literal(oid.to_der()?);
        self.push_tag(None, &Tag::Oid, |builder| {
            builder.push_byte_array(None, &val)
        })
    }

    fn push_bitstring(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        bits: &[Value<bool>],
    ) -> Result<()> {
        let bits = bits
            .iter()
            .map(Self::get_value_or_error)
            .collect::<Result<Vec<_>>>()?;
        // See X.690 spec section 8.6 for encoding details.
        // Note: the encoding of an empty bitstring must be the number of unused bits to 0 and have no content.
        let nr_bytes = (bits.len() + 7) / 8;
        let mut bytes = vec![0u8; nr_bytes];
        for (i, bit) in bits.iter().enumerate() {
            bytes[i / 8] |= (**bit as u8) << (7 - (i % 8));
        }

        self.push_as_bit_string(None, tag, bytes.len() * 8 - bits.len(), |builder| {
            builder.push_byte_array(name_hint.clone(), &Value::Literal(bytes.clone()))
        })
    }

    /// Push tagged content into the ASN1 output. The closure can use any available function of the builder
    /// and produces the content of the tagged data.
    fn push_tag(
        &mut self,
        _name_hint: Option<String>,
        tag: &Tag,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        let mut content = Der::new();
        gen(&mut content)?;
        // Push identifier octets.
        self.push_bytes(&tag.to_der()?)?;
        // Push length, see X.690 section 8.1.3.
        if content.output.len() <= 0x7f {
            self.push_byte(content.output.len() as u8)?;
        } else {
            let mut len = content.output.len();
            let mut bytes = Vec::<u8>::new();
            while len != 0 {
                bytes.push((len & 0xff) as u8);
                len >>= 8;
            }
            self.push_byte(0x80 | (bytes.len() as u8))?;
            bytes.reverse();
            self.push_bytes(&bytes)?;
        }
        // Push content
        self.push_bytes(&content.output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::FromPrimitive;

    #[test]
    fn test_asn1_der_byte() -> Result<()> {
        let der = Der::generate(|builder| builder.push_byte(0xa5))?;
        const RESULT: &[u8] = &[0xa5];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_byte_array() -> Result<()> {
        let bytes: Vec<u8> = vec![0x12, 0x34, 0x56, 0x78];
        let der =
            Der::generate(|builder| builder.push_byte_array(None, &Value::Literal(bytes.clone())))?;
        assert_eq!(der, bytes);
        Ok(())
    }

    #[test]
    fn test_asn1_der_boolean() -> Result<()> {
        let der = Der::generate(|builder| {
            builder.push_boolean(&Tag::Boolean, &Value::Literal(true))?;
            builder.push_boolean(&Tag::Integer, &Value::Literal(false))
        })?;
        const RESULT: &[u8] = &[
            // Identifier octet (universal, boolean), length, content (can be any nonzero value, our DER generator uses 0xff).
            0x01, 0x01, 0xff, // Identifier octet (universal, integer), length, content.
            0x02, 0x01, 0x00,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_integer() -> Result<()> {
        let der = Der::generate(|builder| {
            builder.push_integer(
                None,
                &Tag::Integer,
                &Value::Literal(BigUint::from_u32(0).unwrap()),
            )?;
            builder.push_integer(
                None,
                &Tag::Integer,
                &Value::Literal(BigUint::from_u32(0x1234).unwrap()),
            )?;
            builder.push_integer(
                None,
                &Tag::OctetString,
                &Value::Literal(BigUint::from_u32(0x8000).unwrap()),
            )
        })?;
        const RESULT: &[u8] = &[
            // Identifier octet (universal, integer), length, content (minimal encoding, always uses one byte at least).
            0x02, 0x01, 0x0,
            // Identifier octet (universal, integer), length, content (minimal encoding).
            0x02, 0x02, 0x12, 0x34,
            // Identifier octet (universal, octet string), length, content (minimal encoding, needs 0x00 because MSB is set).
            0x04, 0x03, 0x00, 0x80, 0x00,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_integer_pad() -> Result<()> {
        let der = Der::generate(|builder| {
            builder.push_integer_pad(
                None,
                &Value::Literal(BigUint::from_u32(0x1234).unwrap()),
                2,
            )?;
            builder.push_integer_pad(None, &Value::Literal(BigUint::from_u32(0x1234).unwrap()), 4)
        })?;
        const RESULT: &[u8] = &[
            // Content.
            0x12, 0x34, // Content.
            0x00, 0x00, 0x12, 0x34,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_string() -> Result<()> {
        let der = Der::generate(|builder| {
            builder.push_string(
                None,
                &Tag::PrintableString,
                &Value::Literal("lowRISC".into()),
            )?;
            builder.push_string(None, &Tag::Utf8String, &Value::Literal("OpenTitan".into()))?;
            builder.push_string(None, &Tag::OctetString, &Value::Literal("".into()))
        })?;
        const RESULT: &[u8] = &[
            // Identifier octet (universal, printable string), length, content.
            0x13, 0x07, 0x6c, 0x6f, 0x77, 0x52, 0x49, 0x53, 0x43,
            // Identifier octet (universal, integer), length, content.
            0x0c, 0x09, 0x4f, 0x70, 0x65, 0x6e, 0x54, 0x69, 0x74, 0x61, 0x6e,
            // Identifier octet (universal, integer), length, no content.
            0x04, 0x00,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_oid() -> Result<()> {
        let der = Der::generate(|builder| builder.push_oid(&Oid::Custom("2.999.3".into())))?;
        const RESULT: &[u8] = &[
            // Identifier octet (universal, OID), length, content (encoded as per X.690 section 8.19.5).
            0x06, 0x03, 0x88, 0x037, 0x03,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_bitstring() -> Result<()> {
        let der = Der::generate(|builder| {
            builder.push_bitstring(None, &Tag::BitString, &[])?;
            builder.push_bitstring(None, &Tag::BitString, &[Value::Literal(true)])?;
            builder.push_bitstring(None, &Tag::OctetString, &[Value::Literal(false)])?;
            builder.push_bitstring(
                None,
                &Tag::BitString,
                &[
                    true, false, true, true, false, false, false, false, true, false, false, true,
                ]
                .into_iter()
                .map(Value::Literal)
                .collect::<Vec<_>>(),
            )
        })?;
        const RESULT: &[u8] = &[
            // Identifier octet (bitstring, OID), length, content (encoded as per X.690 section 8.6).
            0x03, 0x01, 0x0, // Identifier octet (bitstring, OID), length, content.
            0x03, 0x02, 0x7, 0x80, // Identifier octet (bitstring, OID), length, content.
            0x04, 0x02, 0x7, 0x00,
            // Identifier octet (bitstring, OID), length, content (written in binary to make it easier to read).
            0x03, 0x03, 0x04, 0b10110000, 0b10010000,
        ];
        assert_eq!(&der, RESULT);
        Ok(())
    }

    #[test]
    fn test_asn1_der_tag() -> Result<()> {
        // Pairs of (data, encoding of length)
        let bytes_empty: (&[u8], &[u8]) = (&[], &[0x00]);
        let bytes_short: (&[u8], &[u8]) = (&[0xa5u8; 0x7f], &[0x7f]);
        let bytes_long_1a: (&[u8], &[u8]) = (&[0xb6u8; 0x80], &[0x81, 0x80]);
        let bytes_long_1b: (&[u8], &[u8]) = (&[0xc7u8; 0xff], &[0x81, 0xff]);
        let bytes_long_2a: (&[u8], &[u8]) = (&[0xd8u8; 0x100], &[0x82, 0x01, 0x00]);
        let bytes_long_2b: (&[u8], &[u8]) = (&[0xe9u8; 0xffff], &[0x82, 0xff, 0xff]);
        let seq = [
            bytes_empty,
            bytes_short,
            bytes_long_1a,
            bytes_long_1b,
            bytes_long_2a,
            bytes_long_2b,
        ];
        let der = Der::generate(|builder| {
            for (bytes, _) in seq {
                builder.push_tag(None, &Tag::Sequence, |builder| {
                    builder.push_byte_array(None, &Value::Literal(bytes.to_vec()))
                })?;
            }
            Ok(())
        })?;
        let mut result = Vec::<u8>::new();
        for (bytes, len_enc) in seq {
            result.push(0x30); // Identifier octet (universal, sequence).
            result.extend(len_enc);
            result.extend(bytes);
        }
        assert_eq!(der, result);
        Ok(())
    }
}
