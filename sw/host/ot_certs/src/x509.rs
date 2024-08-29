// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use indexmap::IndexMap;
use num_bigint_dig::BigUint;

use foreign_types::ForeignTypeRef;
use openssl::asn1::{
    Asn1IntegerRef, Asn1ObjectRef, Asn1OctetStringRef, Asn1StringRef, Asn1TimeRef,
};
use openssl::bn::{BigNum, BigNumContext, BigNumRef};
use openssl::ec::{EcGroupRef, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::nid::Nid;
use openssl::pkey::PKey;
use openssl::pkey::Public;
use openssl::x509::{X509NameRef, X509};

use crate::asn1::der;
use crate::asn1::x509;

use crate::template::{
    self, AttributeType, EcCurve, EcPublicKeyInfo, EcdsaSignature, KeyUsage, Name, Signature,
    SubjectPublicKeyInfo, Value,
};

pub mod extension;

fn curve_from_ecgroup(group: &EcGroupRef) -> Result<EcCurve> {
    let Some(name) = group.curve_name() else {
        bail!("only curves with standard names are supported")
    };
    match name {
        Nid::X9_62_PRIME256V1 => Ok(EcCurve::Prime256v1),
        _ => bail!("curve {:?} is not supported", name),
    }
}

impl TryFrom<&Asn1ObjectRef> for AttributeType {
    type Error = anyhow::Error;

    fn try_from(obj: &Asn1ObjectRef) -> Result<AttributeType, Self::Error> {
        // Try to match attriutes that OpenSSL does not known about.
        for attr in [
            AttributeType::TpmVendor,
            AttributeType::TpmModel,
            AttributeType::TpmVersion,
        ] {
            if obj.to_owned().as_slice() == attr.oid().to_der().unwrap().as_slice() {
                return Ok(attr);
            }
        }
        Ok(match obj.nid() {
            Nid::COUNTRYNAME => AttributeType::Country,
            Nid::ORGANIZATIONNAME => AttributeType::Organization,
            Nid::ORGANIZATIONALUNITNAME => AttributeType::OrganizationalUnit,
            Nid::STATEORPROVINCENAME => AttributeType::State,
            Nid::COMMONNAME => AttributeType::CommonName,
            Nid::SERIALNUMBER => AttributeType::SerialNumber,
            _ => bail!("unrecognized OID {:?}", obj),
        })
    }
}

fn asn1int_to_bn(field: &str, bn: &Asn1IntegerRef) -> Result<Value<BigUint>> {
    Ok(Value::literal(BigUint::from_bytes_be(
        &bn.to_bn()
            .with_context(|| format!("could not extract {} from certificate", field))?
            .to_vec(),
    )))
}

fn asn1bignum_to_bn(bn: &BigNumRef) -> Value<BigUint> {
    Value::literal(BigUint::from_bytes_be(&bn.to_vec()))
}

fn asn1str_to_str(field: &str, s: &Asn1StringRef) -> Result<Value<String>> {
    Ok(Value::literal(
        s.as_utf8()
            .with_context(|| format!("could not extract {} from certificate", field))?
            .to_string(),
    ))
}

fn asn1octets_to_vec(s: &Asn1OctetStringRef) -> Value<Vec<u8>> {
    Value::literal(s.as_slice().to_vec())
}

fn asn1time_to_string(time: &Asn1TimeRef) -> Result<Value<String>> {
    // OpenSSL guarantees that an ASN1_TIME is in fact just a typedef for ASN1_STRING
    // https://www.openssl.org/docs/man1.1.1/man3/ASN1_TIME_to_generalizedtime.html
    let time_str = time.as_ptr() as *mut openssl_sys::ASN1_STRING;
    // SAFETY: the above pointer is guaranteed to be valid since `time` is valid reference.
    let time_type = unsafe { openssl_sys::ASN1_STRING_type(time_str) };
    // FIXME: we only support GeneralizedTime and openssl_sys does not export the OpenSSL method to
    // convert to a GeneralizedTime so we just error out.
    if time_type == openssl_sys::V_ASN1_UTCTIME {
        bail!("time uses UtcTime but only GeneralizedTime is supported")
    }
    if time_type != openssl_sys::V_ASN1_GENERALIZEDTIME {
        bail!("time uses type {time_type} but only GeneralizedTime is supported")
    }
    // SAFETY: the above pointer is guaranteed to be valid since `time` is valid reference.
    let time_str = unsafe { Asn1StringRef::from_ptr(time_str) }.as_slice();
    Ok(Value::literal(
        std::str::from_utf8(time_str)
            .context("GeneralizedTime is not a valid UTF8 string")?
            .to_string(),
    ))
}

fn asn1name_to_name(field: &str, name: &X509NameRef) -> Result<Name> {
    // FIXME The OpenSSL representation of names is a bit odd: it flattens
    // the sequence of sets into a sequence but for each name entry remembers
    // the index into the sequence. Unfortunately, we need to call X509_NAME_ENTRY_set
    // to get the index but this is not exported by openssl-sys. For now, and since
    // multi-valued RDNs are rare, simply assume that all sets have size 1.
    let mut name_res = Name::new();
    for entry in name.entries() {
        let attr = AttributeType::try_from(entry.object())?;
        let mut res = IndexMap::new();
        res.insert(attr, asn1str_to_str(field, entry.data())?);
        name_res.push(res)
    }
    Ok(name_res)
}

fn extract_ec_pubkey(eckey: &EcKey<Public>) -> Result<EcPublicKeyInfo> {
    let mut ctx = BigNumContext::new().unwrap();
    let mut x = BigNum::new().unwrap();
    let mut y = BigNum::new().unwrap();
    eckey
        .public_key()
        .affine_coordinates(eckey.group(), &mut x, &mut y, &mut ctx)
        .unwrap();
    Ok(template::EcPublicKeyInfo {
        curve: curve_from_ecgroup(eckey.group())?,
        public_key: template::EcPublicKey {
            x: asn1bignum_to_bn(&x),
            y: asn1bignum_to_bn(&y),
        },
    })
}

fn extract_pub_key(pubkey: &PKey<Public>) -> Result<SubjectPublicKeyInfo> {
    match pubkey.id() {
        openssl::pkey::Id::EC => Ok(SubjectPublicKeyInfo::EcPublicKey(extract_ec_pubkey(
            &pubkey.ec_key().unwrap(),
        )?)),
        id => bail!("key type {:?} not supported by the parser", id),
    }
}

fn extract_ecdsa_signature(x509: &X509) -> Result<EcdsaSignature> {
    let ecdsa_sig = EcdsaSig::from_der(x509.signature().as_slice())
        .context("cannot extract ECDSA signature from certificate")?;
    Ok(EcdsaSignature {
        r: asn1bignum_to_bn(ecdsa_sig.r()),
        s: asn1bignum_to_bn(ecdsa_sig.s()),
    })
}

fn extract_signature(x509: &X509) -> Result<Signature> {
    match x509.signature_algorithm().object().nid() {
        Nid::ECDSA_WITH_SHA256 => Ok(Signature::EcdsaWithSha256 {
            value: Some(extract_ecdsa_signature(x509)?),
        }),
        alg => bail!("unsupported signature algorithm {:?}", alg),
    }
}

/// Generate a X509 certificate from a pre-computed TBS and signature.
pub fn generate_certificate_from_tbs(tbs: Vec<u8>, signature: &Signature) -> Result<Vec<u8>> {
    // Generate certificate.
    let tbs = Value::Literal(tbs);
    let cert =
        der::Der::generate(|builder| x509::X509::push_certificate(builder, &tbs, signature))?;
    Ok(cert)
}

/// Generate a X509 certificate from a template that specifies all variables.
/// If the template does not specify the values of the signature, a signature
/// with "zero" values will be generated.
pub fn generate_certificate(tmpl: &template::Template) -> Result<Vec<u8>> {
    // Generate TBS.
    let tbs =
        der::Der::generate(|builder| x509::X509::push_tbs_certificate(builder, &tmpl.certificate))?;
    let tbs = Value::Literal(tbs);
    // Generate certificate.
    let cert = der::Der::generate(|builder| {
        x509::X509::push_certificate(builder, &tbs, &tmpl.certificate.signature)
    })?;
    Ok(cert)
}

fn get_subject_alt_name(x509: &X509) -> Result<Name> {
    let Some(names) = x509.subject_alt_names() else {
        return Ok(Name::default());
    };
    // We expect a single general name.
    let mut iter = names.iter();
    let Some(general_name) = iter.next() else {
        return Ok(Name::default());
    };
    ensure!(
        iter.next().is_none(),
        "only one general name is supported for subject alt names"
    );
    let x509_name_ref = general_name
        .directory_name()
        .context("only directory names are supported for subject alt names")?;
    asn1name_to_name("Subject Alternative Names", x509_name_ref)
}

/// Parse a X509 certificate
pub fn parse_certificate(cert: &[u8]) -> Result<template::Certificate> {
    let x509 = X509::from_der(cert).context("could not parse certificate with openssl")?;
    let raw_extensions =
        extension::x509_get_extensions(&x509).context("could not parse X509 extensions")?;
    let mut private_extensions = Vec::new();
    let mut basic_constraints = None;
    let mut key_usage: Option<KeyUsage> = None;
    for ext in raw_extensions {
        match ext.object.nid() {
            // Ignore extensions that are standard and handled by openssl.
            Nid::BASIC_CONSTRAINTS => {
                ensure!(
                    basic_constraints.is_none(),
                    "certificate contains several basic constraints extensions"
                );
                basic_constraints = Some(
                    extension::parse_basic_constraints(&ext)
                        .context("could not parse X509 basic constraints")?,
                );
            }
            Nid::KEY_USAGE => {
                key_usage = Some(
                    extension::parse_key_usage(&ext).context("could not parse X509 key usage")?,
                );
            }
            Nid::AUTHORITY_KEY_IDENTIFIER => (),
            Nid::SUBJECT_ALT_NAME => (),
            Nid::SUBJECT_KEY_IDENTIFIER => (),
            _ => private_extensions
                .push(extension::parse_extension(&ext).context("could not parse X509 extension")?),
        }
    }

    let subject_public_key_info = extract_pub_key(
        &x509
            .public_key()
            .context("the X509 does not have a valid public key!")?,
    )?;

    Ok(template::Certificate {
        serial_number: asn1int_to_bn("serial number", x509.serial_number())?,
        issuer: asn1name_to_name("issuer", x509.issuer_name())?,
        subject: asn1name_to_name("subject", x509.subject_name())?,
        not_before: asn1time_to_string(x509.not_before())
            .context("cannot parse not_before time")?,
        not_after: asn1time_to_string(x509.not_after()).context("cannot parse not_after time")?,
        subject_public_key_info,
        authority_key_identifier: asn1octets_to_vec(
            x509.authority_key_id()
                .context("the certificate has not authority key id")?,
        ),
        subject_key_identifier: asn1octets_to_vec(
            x509.subject_key_id()
                .context("the certificate has not subject key id")?,
        ),
        basic_constraints,
        key_usage,
        subject_alt_name: get_subject_alt_name(&x509)?,
        private_extensions,
        signature: extract_signature(&x509)?,
    })
}
