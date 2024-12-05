// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use num_bigint_dig::BigUint;
use num_traits::FromPrimitive;

use crate::asn1::builder::{concat_suffix, Builder};
use crate::asn1::{Oid, Tag};
use crate::template::{
    AttributeType, BasicConstraints, Certificate, CertificateExtension, EcCurve, EcPublicKeyInfo,
    EcdsaSignature, HashAlgorithm, KeyUsage, Name, Signature, SubjectPublicKeyInfo, Value,
};

impl HashAlgorithm {
    // Return the object identifier of this algorithm.
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
    // Return the object identifier of this attribute type.
    pub fn oid(&self) -> Oid {
        match self {
            Self::Country => Oid::Country,
            Self::Organization => Oid::Organization,
            Self::OrganizationalUnit => Oid::OrganizationalUnit,
            Self::State => Oid::State,
            Self::CommonName => Oid::CommonName,
            Self::SerialNumber => Oid::SerialNumber,
            Self::TpmModel => Oid::SalTpmModel,
            Self::TpmVendor => Oid::SalTpmVendor,
            Self::TpmVersion => Oid::SalTpmVersion,
        }
    }

    // Return the tag of the value associated with this attribute type.
    pub fn data_type(&self) -> Tag {
        match self {
            Self::Country => Tag::PrintableString,
            Self::Organization => Tag::Utf8String,
            Self::OrganizationalUnit => Tag::Utf8String,
            Self::State => Tag::Utf8String,
            Self::CommonName => Tag::Utf8String,
            Self::SerialNumber => Tag::PrintableString,
            Self::TpmModel => Tag::Utf8String,
            Self::TpmVendor => Tag::Utf8String,
            Self::TpmVersion => Tag::Utf8String,
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
            Self::push_validity(builder, &cert.not_before, &cert.not_after)?;
            Self::push_name(builder, Some("subject".into()), &cert.subject)?;
            Self::push_public_key_info(builder, &cert.subject_public_key_info)?;
            builder.push_tag(
                Some("tbs_extensions_tag".into()),
                &Tag::Context {
                    constructed: true,
                    value: 3,
                },
                |builder| {
                    builder.push_seq(Some("tbs_extensions".into()), |builder| {
                        if let Some(constraints) = &cert.basic_constraints {
                            Self::push_basic_constraints_ext(builder, constraints)?;
                        }
                        Self::push_subject_alt_name_ext(builder, &cert.subject_alt_name)?;
                        if let Some(key_usage) = &cert.key_usage {
                            Self::push_key_usage_ext(builder, key_usage)?;
                        }
                        if let Some(auth_key_id) = &cert.authority_key_identifier {
                            Self::push_auth_key_id_ext(builder, auth_key_id)?;
                        }
                        if let Some(subj_key_id) = &cert.subject_key_identifier {
                            Self::push_subject_key_id_ext(builder, subj_key_id)?;
                        }
                        for ext in &cert.private_extensions {
                            Self::push_cert_extension(builder, ext)?
                        }
                        Ok(())
                    })
                },
            )
        })
    }

    pub fn push_cert_extension<B: Builder>(
        builder: &mut B,
        ext: &CertificateExtension,
    ) -> Result<()> {
        match ext {
            CertificateExtension::DiceTcbInfo(dice_ext) => dice_ext.push_extension(builder),
        }
    }

    pub fn push_name<B: Builder>(
        builder: &mut B,
        name_hint: Option<String>,
        name: &Name,
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
            for attributes in name {
                builder.push_set(concat_suffix(&name_hint, "set"), |builder| {
                    for (attr_type, val) in attributes {
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
                        )?;
                    }
                    Ok(())
                })?;
            }
            Ok(())
        })
    }

    pub fn push_basic_constraints_ext<B: Builder>(
        builder: &mut B,
        constraints: &BasicConstraints,
    ) -> Result<()> {
        // https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
        // BasicConstraints ::= SEQUENCE {
        //   cA                      BOOLEAN DEFAULT FALSE,
        //   pathLenConstraint       INTEGER (0..MAX) OPTIONAL }

        // Retrieve the configured value of the extension.
        Self::push_extension(builder, &Oid::BasicConstraints, true, |builder| {
            builder.push_seq(Some("basic_constraints".into()), |builder| {
                builder.push_boolean(&Tag::Boolean, &constraints.ca)
            })
        })
    }

    pub fn push_subject_alt_name_ext<B: Builder>(
        builder: &mut B,
        subject_alt_name: &Name,
    ) -> Result<()> {
        // SubjectAltName ::= GeneralNames
        //
        // GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName
        //
        // GeneralName ::= CHOICE {
        //     otherName                       [0]     OtherName,
        //     rfc822Name                      [1]     IA5String,
        //     dNSName                         [2]     IA5String,
        //     x400Address                     [3]     ORAddress,
        //     directoryName                   [4]     Name,
        //     ediPartyName                    [5]     EDIPartyName,
        //     uniformResourceIdentifier       [6]     IA5String,
        //     iPAddress                       [7]     OCTET STRING,
        //     registeredID                    [8]     OBJECT IDENTIFIER }
        //
        // We only support `directoryName` at the moment.
        if subject_alt_name.is_empty() {
            // Subject Alternative Name is an optional extension, it's ok not to be present.
            return Ok(());
        }
        Self::push_extension(builder, &Oid::SubjectAltName, false, |builder| {
            builder.push_seq(Some("subject_alt_name".into()), |builder| -> Result<()> {
                builder.push_tag(
                    None,
                    &Tag::Context {
                        constructed: true,
                        value: 4,
                    },
                    |builder| -> Result<()> { Self::push_name(builder, None, subject_alt_name) },
                )
            })
        })
    }

    pub fn push_key_usage_ext<B: Builder>(builder: &mut B, key_usage: &KeyUsage) -> Result<()> {
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
        Self::push_extension(builder, &Oid::KeyUsage, true, |builder| {
            builder.push_bitstring(
                Some("key_usage".into()),
                &Tag::BitString,
                &[
                    key_usage
                        .digital_signature
                        .clone()
                        .unwrap_or(Value::literal(false)),
                    /* nonRepudiation */ Value::Literal(false),
                    /* keyEncipherment */ Value::Literal(false),
                    /* dataEncipherment */ Value::Literal(false),
                    key_usage
                        .key_agreement
                        .clone()
                        .unwrap_or(Value::literal(false)),
                    key_usage.cert_sign.clone().unwrap_or(Value::literal(false)),
                    /* cRLSign */ Value::Literal(false),
                    /* encipherOnly */ Value::Literal(false),
                    /* decipherOnly */ Value::Literal(false),
                ],
            )
        })
    }

    pub fn push_auth_key_id_ext<B: Builder>(
        builder: &mut B,
        auth_key_id: &Value<Vec<u8>>,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.1
        // AuthorityKeyIdentifier ::= SEQUENCE {
        //   keyIdentifier             [0] KeyIdentifier           OPTIONAL,
        //   authorityCertIssuer       [1] GeneralNames            OPTIONAL,
        //   authorityCertSerialNumber [2] CertificateSerialNumber OPTIONAL  }
        //
        // KeyIdentifier ::= OCTET STRING
        //
        // Note: this is part of the implicit tagged modules:
        // https://datatracker.ietf.org/doc/html/rfc5280#appendix-A.2
        Self::push_extension(builder, &Oid::AuthorityKeyIdentifier, false, |builder| {
            builder.push_seq(Some("auth_key_id".into()), |builder| {
                builder.push_tag(
                    Some("key_id".into()),
                    &Tag::Context {
                        constructed: false,
                        value: 0,
                    },
                    |builder| builder.push_byte_array(Some("authority_key_id".into()), auth_key_id),
                )
            })
        })
    }

    pub fn push_subject_key_id_ext<B: Builder>(
        builder: &mut B,
        auth_key_id: &Value<Vec<u8>>,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.2
        // KeyIdentifier ::= OCTET STRING
        Self::push_extension(builder, &Oid::SubjectKeyIdentifier, false, |builder| {
            builder.push_octet_string(Some("subject_key_id".into()), |builder| {
                builder.push_byte_array(Some("subject_key_id".into()), auth_key_id)
            })
        })
    }

    pub fn push_extension<B: Builder>(
        builder: &mut B,
        oid: &Oid,
        critical: bool,
        gen: impl FnOnce(&mut B) -> Result<()>,
    ) -> Result<()> {
        // From https://datatracker.ietf.org/doc/html/rfc5280#section-4.1:
        // Extension  ::=  SEQUENCE  {
        //         extnID      OBJECT IDENTIFIER,
        //         critical    BOOLEAN DEFAULT FALSE,
        //         extnValue   OCTET STRING
        //                     -- contains the DER encoding of an ASN.1 value
        //                     -- corresponding to the extension type identified
        //                     -- by extnID
        //         }
        builder.push_seq(concat_suffix(&Some(oid.to_string()), "ext"), |builder| {
            builder.push_oid(oid)?;
            builder.push_boolean(&Tag::Boolean, &Value::Literal(critical))?;
            builder.push_octet_string(concat_suffix(&Some(oid.to_string()), "ext_value"), gen)
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

    pub fn push_validity<B: Builder>(
        builder: &mut B,
        not_before: &Value<String>,
        not_after: &Value<String>,
    ) -> Result<()> {
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
        builder.push_seq(Some("validity".into()), |builder| {
            builder.push_string(Some("not_before".into()), &Tag::GeneralizedTime, not_before)?;
            builder.push_string(Some("not_after".into()), &Tag::GeneralizedTime, not_after)
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
