// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use num_bigint_dig::BigUint;

use foreign_types::{ForeignType, ForeignTypeRef};
use openssl::asn1::{Asn1Object, Asn1ObjectRef, Asn1OctetStringRef};
use openssl::x509::X509;

use crate::asn1::Oid;
use crate::template::{
    BasicConstraints, CertificateExtension, DiceTcbInfoExtension, DiceTcbInfoFlags, FirmwareId,
    HashAlgorithm, KeyUsage, Value,
};

/// X509 extension reference.
pub struct X509ExtensionRef<'a> {
    // Extension type.
    pub object: &'a Asn1ObjectRef,
    // Critical marker.
    pub critical: bool,
    // Extension data.
    pub data: &'a Asn1OctetStringRef,
}

/// Return the list of extensions of an X509 cerificate.
pub fn x509_get_extensions(x509: &X509) -> Result<Vec<X509ExtensionRef>> {
    let mut exts = Vec::new();
    // SAFETY: the rust openssl binding guarantees that x509 is a valid object.
    let ext_count = unsafe { openssl_sys::X509_get_ext_count(x509.as_ptr()) };

    for index in 0..ext_count {
        // SAFETY: the rust openssl binding guarantees that x509 is a valid object
        // and `index` is a valid index.
        // From the documentation of X509_get_ext:
        // The returned extension is an internal pointer which must not be freed
        // up by the application. Therefore this pointer is valid as long as the X509
        // object lives.
        let ext = unsafe { openssl_sys::X509_get_ext(x509.as_ptr(), index) };

        // SAFETY: `ext` is a valid object.
        let critical = unsafe { openssl_sys::X509_EXTENSION_get_critical(ext) };
        // In the ASN1, the critical marker is a boolean so it's actually impossible for
        // openssl to return anything but 0 and 1, so throw in error in case we see anything else.
        let critical = match critical {
            0 => false,
            1 => true,
            _ => bail!("openssl returned non-boolean critical marker for extension {index}"),
        };

        // SAFETY: `ext` is a valid object and the returned pointer is marked with the lifetime
        // of the X509 object that owns the memory.
        let object = unsafe {
            // From the documentation of X509_EXTENSION_get_data:
            // The returned pointer is an internal value which must not be freed up.
            let data = openssl_sys::X509_EXTENSION_get_object(ext);
            Asn1ObjectRef::from_ptr(data)
        };

        // SAFETY: `ext` is a valid object and the returned pointer is marked with the lifetime
        // of the X509 object that owns the memory.
        let data = unsafe {
            // From the documentation of X509_EXTENSION_get_data:
            // The returned pointer is an internal value which must not be freed up.
            let data = openssl_sys::X509_EXTENSION_get_data(ext);
            Asn1OctetStringRef::from_ptr(data)
        };

        exts.push(X509ExtensionRef {
            object,
            critical,
            data,
        })
    }

    Ok(exts)
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

// See DiceTcbInfo.
#[derive(asn1::Asn1Read)]
struct Fwid<'a> {
    pub hash_alg: asn1::ObjectIdentifier,
    pub digest: &'a [u8],
}

// This is an internal structure used to parse a DiceTcbInfo extension using the `asn1`
// crate. We cannot use the `DiceTcbInfoExtension` in `template` since we
// need to use specific annotations and types so that the `asn` library can
// derive an ASN1 parser.
#[derive(asn1::Asn1Read)]
struct DiceTcbInfo<'a> {
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
    pub flags: Option<DiceTcbInfoFlags>,
    #[implicit(8)]
    pub vendor_info: Option<&'a [u8]>,
    #[implicit(9)]
    pub tcb_type: Option<&'a [u8]>,
}

fn convert_hash_algorithm(objid: &asn1::ObjectIdentifier) -> Result<HashAlgorithm> {
    for (oid, hashalg) in [(Oid::Sha256, HashAlgorithm::Sha256)] {
        if *objid
            == asn1::ObjectIdentifier::from_string(oid.oid())
                .expect("Cannot convert Oid to asn1::ObjectIdentifier")
        {
            return Ok(hashalg);
        }
    }
    bail!("unsupported hash algorithm {}", objid);
}

fn asn1utf8_to_str(s: &asn1::Utf8String) -> Value<String> {
    Value::literal(s.as_str().to_string())
}

fn asn1bigint_to_bn(bn: &asn1::BigInt) -> Value<BigUint> {
    Value::literal(BigUint::from_bytes_be(bn.as_bytes()))
}

impl DiceTcbInfo<'_> {
    fn to_dice_extension(&self) -> Result<DiceTcbInfoExtension> {
        let fw_ids = self
            .fwids
            .as_ref()
            .map(|fwids| {
                fwids
                    .clone()
                    .map(|fwid| {
                        Ok(FirmwareId {
                            hash_algorithm: convert_hash_algorithm(&fwid.hash_alg)
                                .context("unknown hash algorithm")?,
                            digest: Value::literal(fwid.digest.to_vec()),
                        })
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()
            .context("cannot parse DICE TCB firmware IDs")?;

        // Vendor info is not supported.
        ensure!(
            self.index.is_none(),
            "the parser does not support DICE TCB index"
        );
        ensure!(
            self.vendor_info.is_none(),
            "the parser does not support DICE TCB vendor info"
        );
        ensure!(
            self.tcb_type.is_none(),
            "the parser does not support DICE TCB type"
        );

        Ok(DiceTcbInfoExtension {
            model: self.model.as_ref().map(asn1utf8_to_str),
            vendor: self.vendor.as_ref().map(asn1utf8_to_str),
            version: self.version.as_ref().map(asn1utf8_to_str),
            svn: self.svn.as_ref().map(asn1bigint_to_bn),
            layer: self.layer.as_ref().map(asn1bigint_to_bn),
            fw_ids,
            flags: self.flags.clone(),
        })
    }
}

impl<'a> asn1::SimpleAsn1Readable<'a> for DiceTcbInfoFlags {
    const TAG: asn1::Tag = asn1::OwnedBitString::TAG;
    fn parse_data(_data: &'a [u8]) -> asn1::ParseResult<Self> {
        let result = asn1::OwnedBitString::parse_data(_data)?;
        let bs = result.as_bitstring();
        if bs.as_bytes().len() != 1 || bs.padding_bits() != 4 {
            // We expect 4 bits.
            asn1::ParseResult::Err(asn1::ParseError::new(asn1::ParseErrorKind::InvalidLength))
        } else {
            Ok(DiceTcbInfoFlags {
                not_configured: Value::Literal(bs.has_bit_set(0)),
                not_secure: Value::Literal(bs.has_bit_set(1)),
                recovery: Value::Literal(bs.has_bit_set(2)),
                debug: Value::Literal(bs.has_bit_set(3)),
            })
        }
    }
}

// From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
// KeyUsage ::= BIT STRING {
//    digitalSignature        (0),
//    nonRepudiation          (1), -- recent editions of X.509 have
//                         -- renamed this bit to contentCommitment
//    keyEncipherment         (2),
//    dataEncipherment        (3),
//    keyAgreement            (4),
//    keyCertSign             (5),
//    cRLSign                 (6),
//    encipherOnly            (7),
//    decipherOnly            (8) }
impl<'a> asn1::SimpleAsn1Readable<'a> for KeyUsage {
    const TAG: asn1::Tag = asn1::OwnedBitString::TAG;
    fn parse_data(_data: &'a [u8]) -> asn1::ParseResult<Self> {
        let result = asn1::OwnedBitString::parse_data(_data)?;
        let bs = result.as_bitstring();
        // List of bits that this parser supports. Any bit set outside of
        // these will be an error because we cannot record it.
        const PARSED_BITS: &[usize] = &[0, 4, 5];
        let len = bs.as_bytes().len() * 8 - bs.padding_bits() as usize;
        for i in 0..len {
            if bs.has_bit_set(i) && !PARSED_BITS.contains(&i) {
                // FIXME This will not return a very readable error message but the asn1
                // does not support arbitrary string errors.
                return asn1::ParseResult::Err(asn1::ParseError::new(
                    asn1::ParseErrorKind::ExtraData,
                ));
            }
        }
        Ok(KeyUsage {
            digital_signature: Some(Value::Literal(bs.has_bit_set(0))),
            key_agreement: Some(Value::Literal(bs.has_bit_set(4))),
            cert_sign: Some(Value::Literal(bs.has_bit_set(5))),
        })
    }
}

/// Try to parse an X509 extension as a DICE TCB info extension.
pub fn parse_dice_tcb_info_extension(ext: &[u8]) -> Result<DiceTcbInfoExtension> {
    asn1::parse_single::<DiceTcbInfo>(ext)
        .context("cannot parse DICE extension")?
        .to_dice_extension()
}

// This is an internal structure used to parse a Basic Constraints extension using the `asn1`
// crate. We cannot use the `BasicConstraints` in `template` since we
// need to use specific annotations and types so that the `asn` library can
// derive an ASN1 parser.
#[derive(asn1::Asn1Read)]
struct BasicConstraintsInternal {
    ca: bool,
}

impl BasicConstraintsInternal {
    fn to_basic_constraints(&self) -> Result<BasicConstraints> {
        Ok(BasicConstraints {
            ca: Value::Literal(self.ca),
        })
    }
}

pub fn parse_key_usage(ext: &X509ExtensionRef) -> Result<KeyUsage> {
    Ok(asn1::parse_single::<KeyUsage>(ext.data.as_slice())?)
}

pub fn parse_basic_constraints(ext: &X509ExtensionRef) -> Result<BasicConstraints> {
    asn1::parse_single::<BasicConstraintsInternal>(ext.data.as_slice())
        .context("cannot parse DICE extension")?
        .to_basic_constraints()
}

/// Try to parse an X509 extension.
pub fn parse_extension(ext: &X509ExtensionRef) -> Result<CertificateExtension> {
    let dice_oid =
        Asn1Object::from_str(Oid::DiceTcbInfo.oid()).expect("cannot create object ID from string");
    // The openssl library does not provide a way to compare between two Asn1Object so compare the raw DER.
    Ok(match ext.object.to_owned().as_slice() {
        obj if obj == dice_oid.as_slice() => {
            CertificateExtension::DiceTcbInfo(parse_dice_tcb_info_extension(ext.data.as_slice())?)
        }
        _ => bail!("unknown extension type {}", ext.object,),
    })
}
