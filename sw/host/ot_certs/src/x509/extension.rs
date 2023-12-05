// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};

use foreign_types::{ForeignType, ForeignTypeRef};
use openssl::asn1::{Asn1Object, Asn1OctetStringRef};
use openssl::x509::X509;

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
    pub fwids: Option<asn1::SequenceOf<'a, Fwid<'a>>>,
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

const DICE_TCB_EXT_OID: &str = "2.23.133.5.4.1";

pub fn extract_dice_tcb_info_extension(x509: &X509) -> Result<DiceTcbInfo> {
    let dice_oid =
        Asn1Object::from_str(DICE_TCB_EXT_OID).expect("cannot create object ID from string");
    let dice_tcb_ext = x509_get_ext_by_obj(x509, &dice_oid)
        .expect("cannot extract DICE TCB extension from the certificate");
    let dice_tcb_der = dice_tcb_ext.as_slice();
    Ok(asn1::parse_single::<DiceTcbInfo>(dice_tcb_der)?)
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
