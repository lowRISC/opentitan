// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};

pub mod builder;
pub mod codegen;
pub mod der;
pub mod dice_tcb;
pub mod x509;

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
    // X509 extensions.
    AuthorityKeyIdentifier,
    BasicConstraints,
    DiceTcbInfo,
    KeyUsage,
    SubjectKeyIdentifier,
    // Name attributes.
    CommonName,
    Country,
    Organization,
    OrganizationalUnit,
    SerialNumber,
    State,
    // Signature algorithms.
    EcdsaWithSha256,
    // Public key type.
    EcPublicKey,
    // Elliptic curve names.
    Prime256v1,
    // Hash algorithms.
    Sha256,
    // Subject alternative name and its components.
    SubjectAltName,
    // Vendor aka manufacturer.
    SalTpmVendor,
    // Tpm Model (i.e. Ti50).
    SalTpmModel,
    // Tpm firmware version at the time of manufacturing.
    SalTpmVersion,
    // Custom oid.
    Custom(String),
}

impl Oid {
    /// Return the standard notation of the OID as string.
    pub fn oid(&self) -> &str {
        match self {
            // From https://datatracker.ietf.org/doc/html/rfc5280
            // id-ce   OBJECT IDENTIFIER ::=  { joint-iso-ccitt(2) ds(5) 29 }
            //
            // id-ce-basicConstraints OBJECT IDENTIFIER ::=  { id-ce 19 }
            Oid::BasicConstraints => "2.5.29.19",
            // id-ce-keyUsage OBJECT IDENTIFIER ::=  { id-ce 15 }
            Oid::KeyUsage => "2.5.29.15",
            // id-ce-authorityKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 35 }
            Oid::AuthorityKeyIdentifier => "2.5.29.35",
            // id-ce-subjectKeyIdentifier OBJECT IDENTIFIER ::=  { id-ce 14 }
            Oid::SubjectKeyIdentifier => "2.5.29.14",

            // https://trustedcomputinggroup.org/wp-content/uploads/TCG_DICE_Attestation_Architecture_r22_02dec2020.pdf
            // tcg OBJECT IDENTIFIER ::= {2 23 133}
            // tcg-dice OBJECT IDENTIFIER ::= { tcg platformClass(5) 4 }
            // tcg-dice-TcbInfo OBJECT IDENTIFIER ::= {tcg-dice 1}
            Oid::DiceTcbInfo => "2.23.133.5.4.1",

            // From https://www.itu.int/rec/T-REC-X.501/en
            // ID ::= OBJECT IDENTIFIER
            // ds ID ::= {joint-iso-itu-t ds(5)}
            // attributeType ID ::= {ds 4}
            // id-at ID ::= attributeType
            //
            // From https://www.itu.int/rec/T-REC-X.520
            // id-at-commonName OBJECT IDENTIFIER ::= {id-at 3}
            Oid::CommonName => "2.5.4.3",
            // id-at-serialNumber OBJECT IDENTIFIER ::= {id-at 5}
            Oid::SerialNumber => "2.5.4.5",
            // id-at-countryName OBJECT IDENTIFIER ::= {id-at 6}
            Oid::Country => "2.5.4.6",
            // id-at-stateOrProvinceName OBJECT IDENTIFIER ::= {id-at 8}
            Oid::State => "2.5.4.8",
            // id-at-organizationName OBJECT IDENTIFIER ::= {id-at 10}
            Oid::Organization => "2.5.4.10",
            // id-at-organizationalUnitName OBJECT IDENTIFIER ::= {id-at 11}
            Oid::OrganizationalUnit => "2.5.4.11",

            // From https://datatracker.ietf.org/doc/html/rfc5758#section-3.2
            // ecdsa-with-SHA256 OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840)
            //      ansi-X9-62(10045) signatures(4) ecdsa-with-SHA2(3) 2 }
            Oid::EcdsaWithSha256 => "1.2.840.10045.4.3.2",

            // From https://datatracker.ietf.org/doc/html/rfc3279
            // ansi-X9-62  OBJECT IDENTIFIER ::= { iso(1) member-body(2) us(840) 10045 }
            // id-publicKeyType OBJECT IDENTIFIER  ::= { ansi-X9-62 keyType(2) }
            // id-ecPublicKey OBJECT IDENTIFIER ::= { id-publicKeyType 1 }
            Oid::EcPublicKey => "1.2.840.10045.2.1",
            // ellipticCurve OBJECT IDENTIFIER ::= { ansi-X9-62 curves(3) }
            // primeCurve OBJECT IDENTIFIER ::= { ellipticCurve prime(1) }
            // prime256v1  OBJECT IDENTIFIER  ::=  { primeCurve  7 }
            Oid::Prime256v1 => "1.2.840.10045.3.1.7",

            // From https://datatracker.ietf.org/doc/html/rfc5758#section-2
            // id-sha256  OBJECT IDENTIFIER  ::=  { joint-iso-itu-t(2) country(16) us(840)
            //      organization(1) gov(101) csor(3) nistalgorithm(4) hashalgs(2) 1 }
            Oid::Sha256 => "2.16.840.1.101.3.4.2.1",

            // From https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.6
            // subject-alt-name OBJECT_IDENTIFIER ::= { joint-iso-itu-t(2) ds(5)
            //          certificateExtension(29) subjectAltName(17)}
            Oid::SubjectAltName => "2.5.29.17",

            // The following three object IDs come from
            // TCG EK Credential Profile
            // For TPM Family 2.0; Level 0
            // Version 2.5
            // Revision 1
            // January 26, 2022,
            // Section 4  X.509 ASN.1 Structures and OIDs
            // tcg OBJECT IDENTIFIER ::= {
            // joint-iso-itu-t(2) international-organizations(23) tcg(133)
            // tcg-attribute OBJECT IDENTIFIER ::= {tcg 2}
            //
            // tcg-at-tpmManufacturer OBJECT IDENTIFIER ::= {tcg-attribute 1}
            Oid::SalTpmVendor => "2.23.133.2.1",

            // tcg-at-tpmModel OBJECT IDENTIFIER ::= {tcg-attribute 2}
            Oid::SalTpmModel => "2.23.133.2.2",

            // tcg-at-tpmVersion OBJECT IDENTIFIER ::= {tcg-attribute 3}
            Oid::SalTpmVersion => "2.23.133.2.3",

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
