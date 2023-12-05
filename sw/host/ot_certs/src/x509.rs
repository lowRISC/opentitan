// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use num_bigint_dig::BigUint;
use std::collections::HashMap;

use openssl::asn1::{Asn1IntegerRef, Asn1OctetStringRef, Asn1StringRef};
use openssl::bn::{BigNum, BigNumContext, BigNumRef};
use openssl::ec::{EcGroupRef, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::nid::Nid;
use openssl::pkey::PKey;
use openssl::pkey::Public;
use openssl::x509::{X509NameRef, X509};

use crate::template::{
    self, AttributeType, EcCurve, EcPublicKeyInfo, EcdsaSignature, HashAlgorithm, Signature,
    SubjectPublicKeyInfo, Value,
};

mod extension;

fn curve_from_ecgroup(group: &EcGroupRef) -> Result<EcCurve> {
    let Some(name) = group.curve_name() else {
        bail!("only curves with standard names are supported")
    };
    match name {
        Nid::X9_62_PRIME256V1 => Ok(EcCurve::Prime256v1),
        _ => bail!("curve {:?} is not supported", name),
    }
}

impl TryFrom<Nid> for AttributeType {
    type Error = anyhow::Error;

    fn try_from(nid: Nid) -> Result<AttributeType, Self::Error> {
        Ok(match nid {
            Nid::COUNTRYNAME => AttributeType::Country,
            Nid::ORGANIZATIONNAME => AttributeType::Organization,
            Nid::ORGANIZATIONALUNITNAME => AttributeType::OrganizationalUnit,
            Nid::STATEORPROVINCENAME => AttributeType::State,
            Nid::COMMONNAME => AttributeType::CommonName,
            Nid::SERIALNUMBER => AttributeType::SerialNumber,
            _ => bail!("unrecognized OID {:?}", nid),
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

fn asn1bigint_to_bn(bn: &asn1::BigInt) -> Value<BigUint> {
    Value::literal(BigUint::from_bytes_be(bn.as_bytes()))
}

fn asn1str_to_str(field: &str, s: &Asn1StringRef) -> Result<Value<String>> {
    Ok(Value::literal(
        s.as_utf8()
            .with_context(|| format!("could not extract {} from certificate", field))?
            .to_string(),
    ))
}

fn asn1utf8_to_str(s: &asn1::Utf8String) -> Value<String> {
    Value::literal(s.as_str().to_string())
}

fn asn1octets_to_vec(s: &Asn1OctetStringRef) -> Value<Vec<u8>> {
    Value::literal(s.as_slice().to_vec())
}

fn asn1name_to_hashmap(
    field: &str,
    name: &X509NameRef,
) -> Result<HashMap<AttributeType, Value<String>>> {
    let mut res = HashMap::<AttributeType, Value<String>>::new();
    for entry in name.entries() {
        let attr = AttributeType::try_from(entry.object().nid())?;
        if res
            .insert(attr, asn1str_to_str(field, entry.data())?)
            .is_some()
        {
            bail!("bad")
        }
    }
    Ok(res)
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

/// Parse a X509 certificate
pub fn parse_certificate(cert: &[u8]) -> Result<template::Certificate> {
    let x509 = X509::from_der(cert).expect("could not parse certificate with openssl");
    let dice_tcb_info = extension::extract_dice_tcb_info_extension(&x509)
        .expect("could not parse DICE TCB extension");

    let fw_ids = dice_tcb_info.fwids.map(|fwids| {
        fwids
            .clone()
            .map(|fwid| template::FirmwareId {
                hash_algorithm: HashAlgorithm::Sha256,
                digest: Value::literal(fwid.digest.to_vec()),
            })
            .collect::<Vec<_>>()
    });

    // Vendor info is not supported.
    ensure!(
        dice_tcb_info.index.is_none(),
        "the parser does not support DICE index"
    );
    ensure!(
        dice_tcb_info.vendor_info.is_none(),
        "the parser does not support DICE vendor info"
    );
    ensure!(
        dice_tcb_info.tcb_type.is_none(),
        "the parser does not support DICE type"
    );

    let subject_public_key_info = extract_pub_key(
        &x509
            .public_key()
            .expect("the X509 does not have a valid public key!"),
    )?;

    Ok(template::Certificate {
        serial_number: asn1int_to_bn("serial number", x509.serial_number())?,
        issuer: asn1name_to_hashmap("issuer", x509.issuer_name())?,
        subject: asn1name_to_hashmap("subject", x509.subject_name())?,
        subject_public_key_info,
        authority_key_identifier: asn1octets_to_vec(
            x509.authority_key_id()
                .context("the certificate has not authority key id")?,
        ),
        subject_key_identifier: asn1octets_to_vec(
            x509.subject_key_id()
                .context("the certificate has not subject key id")?,
        ),
        model: dice_tcb_info.model.as_ref().map(asn1utf8_to_str),
        vendor: dice_tcb_info.vendor.as_ref().map(asn1utf8_to_str),
        version: dice_tcb_info.version.as_ref().map(asn1utf8_to_str),
        svn: dice_tcb_info.svn.as_ref().map(asn1bigint_to_bn),
        layer: dice_tcb_info.layer.as_ref().map(asn1bigint_to_bn),
        fw_ids,
        flags: dice_tcb_info.flags,
        signature: extract_signature(&x509)?,
    })
}
