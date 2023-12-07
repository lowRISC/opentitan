// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use num_bigint_dig::BigUint;
use num_traits::FromPrimitive;
use std::collections::HashMap;

use crate::asn1::builder::{concat_suffix, Builder};
use crate::asn1::{Oid, Tag};
use crate::template::{
    AttributeType, Certificate, EcCurve, EcPublicKeyInfo, EcdsaSignature, HashAlgorithm, Signature,
    SubjectPublicKeyInfo, Value,
};

impl HashAlgorithm {
    // Return the object indentifier of this algorithm.
    pub fn oid(&self) -> Oid {
        match self {
            HashAlgorithm::Sha256 => Oid::Sha256,
        }
    }
}

impl EcCurve {
    pub fn oid(&self) -> Oid {
        match self {
            EcCurve::Prime256v1 => Oid::Prime256v1,
        }
    }
}

// Those attribute types are described in X.520. For UnboundedDirectoryString,
// we have chosen the UTF-8 type.
impl AttributeType {
    // Return the object indentifier of this attribute type.
    pub fn oid(&self) -> Oid {
        match self {
            Self::Country => Oid::Country,
            Self::Organization => Oid::Organization,
            Self::OrganizationalUnit => Oid::OrganizationalUnit,
            Self::State => Oid::State,
            Self::CommonName => Oid::CommonName,
            Self::SerialNumber => Oid::SerialNumber,
        }
    }

    // Return the tag of the value associated with this attribyte type.
    pub fn data_type(&self) -> Tag {
        match self {
            Self::Country => Tag::PrintableString,
            Self::Organization => Tag::Utf8String,
            Self::OrganizationalUnit => Tag::Utf8String,
            Self::State => Tag::Utf8String,
            Self::CommonName => Tag::Utf8String,
            Self::SerialNumber => Tag::PrintableString,
        }
    }
}

pub struct X509;

impl X509 {
    /// Push an X509 certificate into the builder. The TBS certificate is represented by
    /// a byte array (see push_x509_tbs_certificate).
    pub fn push_certificate<B: Builder>(
        builder: &mut B,
        tbs_cert_var: &Value<Vec<u8>>,
        sig: &Signature,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1:
        // Certificate  ::=  SEQUENCE  {
        //   tbsCertificate       TBSCertificate,
        //   signatureAlgorithm   AlgorithmIdentifier,
        //   signatureValue       BIT STRING }
        builder.push_seq(Some("cert".into()), |builder| {
            builder.push_byte_array(Some("tbs".into()), tbs_cert_var)?;
            Self::push_sig_alg_id(builder, sig)?;
            builder.push_as_bit_string(Some("cert_sig".into()), &Tag::BitString, 0, |builder| {
                Self::push_signature(builder, sig)
            })
        })
    }

    /// Push an X509 TBS certificate into the builder.
    pub fn push_tbs_certificate<B: Builder>(builder: &mut B, cert: &Certificate) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1:
        // TBSCertificate  ::=  SEQUENCE  {
        //   version         [0]  EXPLICIT Version DEFAULT v1,
        //   serialNumber         CertificateSerialNumber,
        //   signature            AlgorithmIdentifier,
        //   issuer               Name,
        //   validity             Validity,
        //   subject              Name,
        //   subjectPublicKeyInfo SubjectPublicKeyInfo,
        //   issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
        //                        -- If present, version MUST be v2 or v3
        //   subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
        //                        -- If present, version MUST be v2 or v3
        //   extensions      [3]  EXPLICIT Extensions OPTIONAL
        //                        -- If present, version MUST be v3
        // }
        //
        // // Version  ::=  INTEGER  {  v1(0), v2(1), v3(2)  }
        //
        // Extensions  ::=  SEQUENCE SIZE (1..MAX) OF Extension
        builder.push_seq(Some("cert".into()), |builder| {
            builder.push_tag(
                Some("tbs_version_tag".into()),
                &Tag::Context {
                    constructed: true,
                    value: 0,
                },
                |builder| {
                    builder.push_integer(
                        Some("tbs_version".into()),
                        &Tag::Integer,
                        &Value::Literal(
                            BigUint::from_u32(2).expect("cannot make biguint from u32"),
                        ),
                    )
                },
            )?;
            // CertificateSerialNumber  ::=  INTEGER
            builder.push_integer(
                Some("tbs_serial_number".into()),
                &Tag::Integer,
                &cert.serial_number,
            )?;
            Self::push_sig_alg_id(builder, &cert.signature)?;
            Self::push_name(builder, Some("issuer".into()), &cert.issuer)?;
            Self::push_validity(builder)?;
            Self::push_name(builder, Some("subject".into()), &cert.subject)?;
            Self::push_public_key_info(builder, &cert.subject_public_key_info)
        })
    }

    pub fn push_name<B: Builder>(
        builder: &mut B,
        name_hint: Option<String>,
        name: &HashMap<AttributeType, Value<String>>,
    ) -> Result<()> {
        // https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
        // Name ::= CHOICE { -- only one possibility for now --
        // rdnSequence  RDNSequence }
        //
        // RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
        //
        // RelativeDistinguishedName ::=
        //     SET SIZE (1..MAX) OF AttributeTypeAndValue
        //
        // AttributeTypeAndValue ::= SEQUENCE {
        //     type     AttributeType,
        //     value    AttributeValue }
        //
        // AttributeType ::= OBJECT IDENTIFIER
        //
        // AttributeValue ::= ANY -- DEFINED BY AttributeType
        builder.push_seq(name_hint.clone(), |builder| {
            for (attr_type, val) in name {
                builder.push_set(concat_suffix(&name_hint, "set"), |builder| {
                    builder.push_seq(
                        concat_suffix(&name_hint, &attr_type.to_string()),
                        |builder| {
                            builder.push_oid(&attr_type.oid())?;
                            builder.push_string(
                                concat_suffix(&name_hint, &attr_type.to_string()),
                                &attr_type.data_type(),
                                val,
                            )
                        },
                    )
                })?;
            }
            Ok(())
        })
    }

    pub fn push_public_key_info<B: Builder>(
        builder: &mut B,
        pubkey_info: &SubjectPublicKeyInfo,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1:
        // SubjectPublicKeyInfo  ::=  SEQUENCE  {
        // algorithm            AlgorithmIdentifier,
        // subjectPublicKey     BIT STRING  }
        builder.push_seq(Some("subject_public_key_info".into()), |builder| {
            Self::push_pubkey_alg_id(builder, pubkey_info)?;
            builder.push_as_bit_string(
                Some("subject_public_key".into()),
                &Tag::BitString,
                0,
                |builder| Self::push_public_key(builder, pubkey_info),
            )
        })
    }

    pub fn push_pubkey_alg_id<B: Builder>(
        builder: &mut B,
        pubkey_info: &SubjectPublicKeyInfo,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.1.2
        // AlgorithmIdentifier  ::=  SEQUENCE  {
        // algorithm               OBJECT IDENTIFIER,
        // parameters              ANY DEFINED BY algorithm OPTIONAL  }
        builder.push_seq(
            Some("subject_public_key_alg".into()),
            |builder| match pubkey_info {
                SubjectPublicKeyInfo::EcPublicKey(ec_pubkey) => {
                    builder.push_oid(&Oid::EcPublicKey)?;
                    Self::push_ec_public_key_params(builder, ec_pubkey)
                }
            },
        )
    }

    pub fn push_public_key<B: Builder>(
        builder: &mut B,
        pubkey_info: &SubjectPublicKeyInfo,
    ) -> Result<()> {
        match pubkey_info {
            SubjectPublicKeyInfo::EcPublicKey(ec_pubkey) => {
                Self::push_ec_public_key(builder, ec_pubkey)
            }
        }
    }

    pub fn push_ec_public_key_params<B: Builder>(
        builder: &mut B,
        pubkey: &EcPublicKeyInfo,
    ) -> Result<()> {
        // From the X9.62 spec: section 6.4
        // Parameters ::= CHOICE {
        //   ecParameters ECParameters,
        //   namedCurve CURVES.&id({CurveNames}),
        //   implicitlyCA NULL
        // }
        //
        // CURVES ::= CLASS {
        //   &id OBJECT IDENTIFIER UNIQUE
        // }
        // WITH SYNTAX { ID &id }
        //
        // CurveNames CURVES ::= {
        //   { ID prime256v1 } | ...
        // }
        //
        builder.push_oid(&pubkey.curve.oid())?;
        Ok(())
    }

    pub fn push_ec_public_key<B: Builder>(builder: &mut B, pubkey: &EcPublicKeyInfo) -> Result<()> {
        // From the X9.62 spec: section 6.2
        // ECPoint ::= OCTET STRING
        //
        // From the X9.62 spec: 4.3.6
        // If P = (x,y), If the uncompressed form is used, then do the following:
        // - Convert the field element x p to an octet string X1.
        // - Convert the field element y to an octet string Y1.
        // - Assign the value 04 to the single octet PC.
        // - The result is the octet string PO = PC || X1 ||Y1.
        // Section 4.3.3 explains how to convert a field element: this is a big-endian
        // integer padded to ceil(log q) bytes.
        //
        // From the X9.62 spec: section 6.4
        // The elliptic curve public key (a value of type ECPoint which is an OCTET STRING) is mapped to a
        // subjectPublicKey (a value of type BIT STRING) as follows: the most significant bit of the OCTET STRING
        // value becomes the most significant bit of the BIT STRING value, etc.; the least significant bit of the OCTET
        // STRING becomes the least significant bit of the BIT STRING.
        let size = match pubkey.curve {
            EcCurve::Prime256v1 => 32,
        };

        builder.push_byte(4)?;
        builder.push_integer_pad(Some("pubkey_ec_x".into()), &pubkey.public_key.x, size)?;
        builder.push_integer_pad(Some("pubkey_ec_y".into()), &pubkey.public_key.y, size)?;
        Ok(())
    }

    pub fn push_validity<B: Builder>(builder: &mut B) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1:
        // Validity ::= SEQUENCE {
        //   notBefore      Time,
        //   notAfter       Time }
        //
        // Time ::= CHOICE {
        //   utcTime        UTCTime,
        //   generalTime    GeneralizedTime }
        //
        // From the X680 spec: section 46
        // GeneralizedTime ::= [UNIVERSAL 24] IMPLICIT VisibleString
        //
        // From the Open Profile for DICE specification:
        // https://pigweed.googlesource.com/open-dice/+/refs/heads/main/docs/specification.md#x_509-cdi-certificates
        // The certificate expiration time is set to a fixed date in the future.
        // The "not before" date is chosen to be in the past since the device does not
        // have a reliable way to get the time.
        builder.push_seq(Some("validity".into()), |builder| {
            builder.push_string(
                Some("not_before".into()),
                &Tag::GeneralizedTime,
                &Value::Literal("20230101000000Z".to_string()),
            )?;
            builder.push_string(
                Some("not_after".into()),
                &Tag::GeneralizedTime,
                &Value::Literal("99991231235959Z".to_string()),
            )
        })
    }

    pub fn push_sig_alg_id<B: Builder>(builder: &mut B, sig: &Signature) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.1.2
        // AlgorithmIdentifier  ::=  SEQUENCE  {
        // algorithm               OBJECT IDENTIFIER,
        // parameters              ANY DEFINED BY algorithm OPTIONAL  }
        //
        // Per the X509 specification, the signature parameters must not contain any parameters
        builder.push_seq(Some("algorithm_identifier".into()), |builder| match sig {
            Signature::EcdsaWithSha256 { .. } => builder.push_oid(&Oid::EcdsaWithSha256),
        })
    }

    pub fn push_signature<B: Builder>(builder: &mut B, sig: &Signature) -> Result<()> {
        match sig {
            Signature::EcdsaWithSha256 { value } => {
                let zero = BigUint::from_u32(0).expect("cannot build BigUint from u32");
                let empty_ecdsa = EcdsaSignature {
                    r: Value::Literal(zero.clone()),
                    s: Value::Literal(zero.clone()),
                };
                Self::push_ecdsa_sig(builder, value.as_ref().unwrap_or(&empty_ecdsa))
            }
        }
    }

    pub fn push_ecdsa_sig<B: Builder>(builder: &mut B, sig: &EcdsaSignature) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc3279#section-2.2.3:
        //
        // Ecdsa-Sig-Value  ::=  SEQUENCE  {
        //  r     INTEGER,
        //  s     INTEGER  }
        builder.push_seq(Some("sig_ecdsa_value".into()), |builder| {
            builder.push_integer(Some("sig_ecdsa_r".into()), &Tag::Integer, &sig.r)?;
            builder.push_integer(Some("sig_ecdsa_s".into()), &Tag::Integer, &sig.s)
        })
    }
}
