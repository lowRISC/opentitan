// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use num_bigint_dig::BigUint;
use std::marker::PhantomData;

use foreign_types::{ForeignType, ForeignTypeRef};
use openssl::asn1::{Asn1Object, Asn1OctetString, Asn1OctetStringRef};
use openssl::x509::{X509Extension, X509};

use crate::template;

// Unfortunately, the rust openssl binding does not have an API to extract arbitrary extension but it exports
// the low level function from the C library to do that.
pub fn x509_get_ext_by_obj<'a>(x509: &'a X509, obj: &Asn1Object) -> Result<&'a Asn1OctetStringRef> {
    // SAFETY: the rust openssl binding guarantees that x509 and obj are valid objects.
    let index = unsafe { openssl_sys::X509_get_ext_by_OBJ(x509.as_ptr(), obj.as_ptr(), -1) };
    if index == -1 {
        bail!("cannot find object in certificate")
    }
    // SAFETY: the rust openssl binding guarantees that x509 is a valid object
    // and index is a valid integer since X509_get_ext_by_OBJ returns either an index
    // or -1.
    let data = unsafe {
        let ext = openssl_sys::X509_get_ext(x509.as_ptr(), index);
        // From the documentation of X509_get_ext:
        // The returned extension is an internal pointer which must not be freed
        // up by the application.
        let data = openssl_sys::X509_EXTENSION_get_data(ext);
        // From the documentation of X509_EXTENSION_get_data:
        // The returned pointer is an internal value which must not be freed up.
        Asn1OctetStringRef::from_ptr(data)
    };
    // The returned pointer is an internal value which must not be freed up.
    Ok(data)
}

// Convert attribute types to openssl name IDs.
pub fn subject_key_id_extension(keyid: &[u8]) -> Result<X509Extension> {
    // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1
    // id-ce   OBJECT IDENTIFIER ::=  { joint-iso-ccitt(2) ds(5) 29 }
    //
    // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.2
    // id-ce-subjectKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 14 }
    // SubjectKeyIdentifier ::= KeyIdentifier
    //
    // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.1
    // KeyIdentifier ::= OCTET STRING
    let der = asn1::write(|w| w.write_element(&keyid))?;
    let octet_string = Asn1OctetString::new_from_bytes(&der)?;
    // Unfortunately, the rust binding does not seem to allow creating a Asn1Object
    // from a Nid so we have to manually create it from the OID string.
    let oid = Asn1Object::from_str("2.5.29.14")?;
    Ok(X509Extension::new_from_der(&oid, false, &octet_string)?)
}

pub fn auth_key_id_extension(keyid: &[u8]) -> Result<X509Extension> {
    // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1
    // id-ce   OBJECT IDENTIFIER ::=  { joint-iso-ccitt(2) ds(5) 29 }
    //
    // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.1
    // id-ce-authorityKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 35 }
    //
    // AuthorityKeyIdentifier ::= SEQUENCE {
    // keyIdentifier             [0] KeyIdentifier           OPTIONAL,
    // authorityCertIssuer       [1] GeneralNames            OPTIONAL,
    // authorityCertSerialNumber [2] CertificateSerialNumber OPTIONAL  }
    //
    // KeyIdentifier ::= OCTET STRING
    //
    // Note: this is part of the implicit tagged modules:
    // https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.2
    #[derive(asn1::Asn1Write)]
    struct AuthorityKeyIdentifier<'a> {
        #[implicit(0)]
        keyid: Option<&'a [u8]>,
    }

    let der = asn1::write_single(&AuthorityKeyIdentifier { keyid: Some(keyid) })?;
    let octet_string = Asn1OctetString::new_from_bytes(&der)?;
    // Unfortunately, the rust binding does not seem to allow creating a Asn1Object
    // from a Nid so we have to manually create it from the OID string.
    let oid = Asn1Object::from_str("2.5.29.35")?;
    Ok(X509Extension::new_from_der(&oid, false, &octet_string)?)
}

// Helper for the asn1 crate that does not support both reading and writing
// ASN1 sequence out of the box.
#[derive(Hash, PartialEq, Eq, Clone)]
pub enum Asn1ReadableOrWritable<'a, T, U> {
    Read(T, PhantomData<&'a ()>),
    Write(U, PhantomData<&'a ()>),
}

impl<'a, T, U> Asn1ReadableOrWritable<'a, T, U> {
    pub fn new_read(v: T) -> Self {
        Asn1ReadableOrWritable::Read(v, PhantomData)
    }

    pub fn new_write(v: U) -> Self {
        Asn1ReadableOrWritable::Write(v, PhantomData)
    }
}

impl<'a, T: asn1::SimpleAsn1Readable<'a>, U> asn1::SimpleAsn1Readable<'a>
    for Asn1ReadableOrWritable<'a, T, U>
{
    const TAG: asn1::Tag = T::TAG;
    fn parse_data(data: &'a [u8]) -> asn1::ParseResult<Self> {
        Ok(Self::new_read(T::parse_data(data)?))
    }
}

impl<'a, T: asn1::SimpleAsn1Writable, U: asn1::SimpleAsn1Writable> asn1::SimpleAsn1Writable
    for Asn1ReadableOrWritable<'a, T, U>
{
    const TAG: asn1::Tag = U::TAG;
    fn write_data(&self, w: &mut asn1::WriteBuf) -> asn1::WriteResult {
        match self {
            Asn1ReadableOrWritable::Read(v, _) => T::write_data(v, w),
            Asn1ReadableOrWritable::Write(v, _) => U::write_data(v, w),
        }
    }
}

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
#[derive(asn1::Asn1Read, asn1::Asn1Write)]
pub struct Fwid<'a> {
    pub hash_alg: asn1::ObjectIdentifier,
    pub digest: &'a [u8],
}

#[derive(asn1::Asn1Read, asn1::Asn1Write)]
pub struct DiceTcbInfo<'a> {
    #[implicit(0)]
    pub vendor: Option<asn1::Utf8String<'a>>,
    #[implicit(1)]
    pub model: Option<asn1::Utf8String<'a>>,
    #[implicit(2)]
    pub version: Option<asn1::Utf8String<'a>>,
    #[implicit(3)]
    pub svn: Option<asn1::BigInt<'a>>,
    #[implicit(4)]
    pub layer: Option<asn1::BigInt<'a>>,
    #[implicit(5)]
    pub index: Option<asn1::BigInt<'a>>,
    #[implicit(6)]
    pub fwids: Option<
        Asn1ReadableOrWritable<
            'a,
            asn1::SequenceOf<'a, Fwid<'a>>,
            asn1::SequenceOfWriter<'a, Fwid<'a>>,
        >,
    >,
    #[implicit(7)]
    pub flags: Option<template::Flags>,
    #[implicit(8)]
    pub vendor_info: Option<&'a [u8]>,
    #[implicit(9)]
    pub tcb_type: Option<&'a [u8]>,
}

impl asn1::SimpleAsn1Writable for template::Flags {
    const TAG: asn1::Tag = asn1::OwnedBitString::TAG;
    fn write_data(&self, w: &mut asn1::WriteBuf) -> asn1::WriteResult {
        let mut val = 0u8;
        if self.not_configured {
            val |= 1 << 7;
        }
        if self.not_secure {
            val |= 1 << 6;
        }
        if self.recovery {
            val |= 1 << 5;
        }
        if self.debug {
            val |= 1 << 4;
        }
        let bitstring = asn1::OwnedBitString::new(vec![val], 4)
            .expect("cannot create an OwnedBitString for flags");
        bitstring.write_data(w)
    }
}

impl<'a> asn1::SimpleAsn1Readable<'a> for template::Flags {
    const TAG: asn1::Tag = asn1::OwnedBitString::TAG;
    fn parse_data(_data: &'a [u8]) -> asn1::ParseResult<Self> {
        let result = asn1::OwnedBitString::parse_data(_data)?;
        let bs = result.as_bitstring();
        if bs.as_bytes().len() != 1 || bs.padding_bits() != 4 {
            // We expect 4 bits.
            asn1::ParseResult::Err(asn1::ParseError::new(asn1::ParseErrorKind::InvalidLength))
        } else {
            Ok(template::Flags {
                not_configured: bs.has_bit_set(0),
                not_secure: bs.has_bit_set(1),
                recovery: bs.has_bit_set(2),
                debug: bs.has_bit_set(3),
            })
        }
    }
}

pub fn dice_tcb_info_extension(dice_tcb_info: &DiceTcbInfo) -> Result<X509Extension> {
    let der = asn1::write_single(dice_tcb_info)?;
    let octet_string = Asn1OctetString::new_from_bytes(&der)?;
    // Unfortunately, the rust binding does not seem to allow creating a Asn1Object
    // from a Nid so we have to manually create it from the OID string.
    let oid = Asn1Object::from_str("2.23.133.5.4.1")?;
    // From DICE specification:
    // The DiceTcbInfo extension SHOULD be marked critical.
    Ok(X509Extension::new_from_der(&oid, true, &octet_string)?)
}

// Extract the signature from an already built and signature
// certificate, and then register the signature variables with
// the generator.
impl template::HashAlgorithm {
    // Return the OID of the hash algorithm.
    pub fn oid(&self) -> asn1::ObjectIdentifier {
        match self {
            // From https://www.rfc-editor.org/rfc/rfc3560.html#appendix-A
            Self::Sha256 => asn1::ObjectIdentifier::from_string("2.16.840.1.101.3.4.2.1").unwrap(),
        }
    }

    // Return the size of the digest.
    pub fn digest_size(&self) -> usize {
        match self {
            Self::Sha256 => 20,
        }
    }
}

// Annoyingly, asn1 only has BigInt and not a owned version.
pub struct Asn1OwnedBigInt {
    data: Vec<u8>,
}

impl Asn1OwnedBigInt {
    pub fn from_biguint(biguint: &BigUint) -> Self {
        // There is a small annoyance here: the asn1 library expects the integer to be minimal
        // and also that if the top most significant bit is set, to prepend a zero byte to avoid
        // ambiguity in the DER encoding.
        let mut data = biguint.to_bytes_le();
        // Remove the MSB until it is not zero. Make sure to never remove all zeros: a valid
        // ASN1 integer must contain at least one byte.
        while data.len() >= 2 && *data.last().unwrap() == 0 {
            data.pop();
        }
        // If the MSB has its its most significant bit set, add a 0 byte.
        if data.last().unwrap().leading_zeros() == 0 {
            data.push(0);
        }
        // The ASN1 representation is in big endian so reverse the data.
        data.reverse();
        Asn1OwnedBigInt { data }
    }

    pub fn to_asn1_bigint(&self) -> asn1::BigInt {
        asn1::BigInt::new(&self.data).expect("asn1::BigInt should never fail in from_biguint")
    }
}
