// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use num_bigint_dig::BigUint;
use std::collections::HashMap;

use openssl::asn1::{Asn1Integer, Asn1IntegerRef, Asn1OctetStringRef, Asn1StringRef, Asn1Time};
use openssl::bn::{BigNum, BigNumContext, BigNumRef};
use openssl::ec::{EcGroup, EcGroupRef, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::hash::MessageDigest;
use openssl::nid::Nid;
use openssl::pkey::PKey;
use openssl::pkey::{Private, Public};
use openssl::x509::extension as openssl_ext;
use openssl::x509::{X509NameBuilder, X509NameRef, X509};

use crate::offsets::{CertificateWithVariables, OffsetGenerator};
use crate::template::{
    self, AttributeType, EcCurve, EcPublicKeyInfo, EcdsaSignature, HashAlgorithm, Signature,
    SubjectPublicKeyInfo, Value,
};

mod extension;
#[cfg(test)]
mod tests;

// Convert a template curve name to an openssl one.
fn ecgroup_from_curve(curve: &EcCurve) -> EcGroup {
    match curve {
        EcCurve::Prime256v1 => EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap(),
    }
}

fn curve_from_ecgroup(group: &EcGroupRef) -> Result<EcCurve> {
    let Some(name) = group.curve_name() else {
        bail!("only curves with standard names are supported")
    };
    match name {
        Nid::X9_62_PRIME256V1 => Ok(EcCurve::Prime256v1),
        _ => bail!("curve {:?} is not supported", name),
    }
}

// Represents a key pair and hash algorithm to sign the certificate.
struct KeyPairHash {
    key_pair: PKey<Private>,
    hash: MessageDigest,
}

impl KeyPairHash {
    // Generate new random ecdsa private/pub key pair.
    fn new_ecdsa_with_hash(curve: &EcCurve, hash: MessageDigest) -> Result<KeyPairHash> {
        let group = ecgroup_from_curve(curve);
        let key = EcKey::<Private>::generate(&group)?;
        let key_pair = PKey::try_from(key)?;
        Ok(KeyPairHash { key_pair, hash })
    }
}

// Convert from a big number to an openssl one.
fn bignum_from_bigint(bigint: &BigUint) -> BigNum {
    BigNum::from_slice(&bigint.to_bytes_be()).unwrap()
}

// Generate a key pair that is compatible the signature algorithm requested.
fn generate_signature_keypair(alg: &Signature) -> Result<KeyPairHash> {
    match alg {
        Signature::EcdsaWithSha256 { .. } => Ok(KeyPairHash::new_ecdsa_with_hash(
            &EcCurve::Prime256v1,
            MessageDigest::sha256(),
        )?),
    }
}

// Same as get_pubkey but specialized for elliptic curves.
fn get_ec_pubkey(
    generator: &mut OffsetGenerator,
    pubkey_info: &template::EcPublicKeyInfo,
) -> Result<PKey<Public>> {
    // The template can either specify both x and y as literal, or as variable but we don't support a mix for both.
    let group = ecgroup_from_curve(&pubkey_info.curve);
    match (&pubkey_info.public_key.x, &pubkey_info.public_key.y) {
        (Value::Literal(x), Value::Literal(y)) => {
            let key = EcKey::<Public>::from_public_key_affine_coordinates(
                &group,
                &bignum_from_bigint(x),
                &bignum_from_bigint(y),
            )
            .context("could not create a public key from provided curve and x,y coordinates")?;
            Ok(PKey::try_from(key)?)
        }
        (Value::Variable(var_x), Value::Variable(var_y)) => {
            // We cannot use random x and y since they need to be on the curve. Generate a random one and
            // register it with the generator.
            let privkey = EcKey::<Private>::generate(&group)?;
            let pubkey = EcKey::<Public>::from_public_key(&group, privkey.public_key())?;
            let mut ctx = BigNumContext::new()?;
            let mut x = BigNum::new()?;
            let mut y = BigNum::new()?;
            privkey
                .public_key()
                .affine_coordinates(&group, &mut x, &mut y, &mut ctx)?;
            // Convert x and y to the DER representation, potentially adding some padding if necessary.
            const EC_X_Y_SIZE: usize = 32;
            generator.register_variable::<BigUint>(
                var_x,
                x.to_vec_padded(EC_X_Y_SIZE.try_into().unwrap())?,
            )?;
            generator.register_variable::<BigUint>(
                var_y,
                y.to_vec_padded(EC_X_Y_SIZE.try_into().unwrap())?,
            )?;
            Ok(PKey::try_from(pubkey)?)
        }
        _ => bail!("you cannot mix literals and variables in the public key for x and y"),
    }
}

// Get the public key from the template, or a generate a random one compatible with
// the algorithm requested.
fn get_or_register_pubkey(
    generator: &mut OffsetGenerator,
    pubkey_info: &SubjectPublicKeyInfo,
) -> Result<PKey<Public>> {
    match pubkey_info {
        SubjectPublicKeyInfo::EcPublicKey(ec_pubkey) => get_ec_pubkey(generator, ec_pubkey),
    }
}

// Convert attribute types to openssl name IDs.
impl AttributeType {
    fn nid(&self) -> Nid {
        match self {
            Self::Country => Nid::COUNTRYNAME,
            Self::Organization => Nid::ORGANIZATIONNAME,
            Self::OrganizationalUnit => Nid::ORGANIZATIONALUNITNAME,
            Self::State => Nid::STATEORPROVINCENAME,
            Self::CommonName => Nid::COMMONNAME,
            Self::SerialNumber => Nid::SERIALNUMBER,
        }
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

// Extract the signature from an already built and signature
// certificate, and then register the signature variables with
// the generator.
fn extract_and_register_signature(
    generator: &mut OffsetGenerator,
    signature: &Signature,
    sigder: &[u8],
) -> Result<()> {
    match signature {
        Signature::EcdsaWithSha256 { value } => {
            let ecdsa_sig = EcdsaSig::from_der(sigder)
                .context("cannot extract ECDSA signature from certificate")?;
            // The ASN1 representation of r and s are as big-endian integers which is what is returned by to_vec.
            let r = ecdsa_sig.r().to_vec();
            let s = ecdsa_sig.s().to_vec();
            // If the template does not specify a value then add hidden variables to clear them.
            if let Some(value) = value {
                // We only support variables and not literals.
                let (Value::Variable(var_r), Value::Variable(var_s)) = (&value.r, &value.s) else {
                    bail!("The generator only supports ecdsa signature templates where 'r' and 's' are variables, not a literals");
                };
                generator.register_variable::<BigUint>(var_r, r)?;
                generator.register_variable::<BigUint>(var_s, s)?;
            } else {
                generator.add_hidden_variable("__hidden_sig_ec_r".to_string(), r);
                generator.add_hidden_variable("__hidden_sig_ec_s".to_string(), s);
            }
            Ok(())
        }
    }
}

/// Generate an X509 certificate using a template certificate and an assignment
/// of the variables to their specific values.
pub fn generate_certificate(
    tmpl: &template::Template,
    clear_fields: bool,
) -> Result<CertificateWithVariables> {
    let mut generator = OffsetGenerator::new(&tmpl.variables);

    let mut builder = X509::builder()?;

    // From the Open Profile for DICE specification:
    // https://pigweed.googlesource.com/open-dice/+/refs/heads/main/docs/specification.md#x_509-cdi-certificates
    // The certificate expiration time is set to a fixed date in the future.
    // The "not before" date is chosen to be in the past since the device does not
    // have a reliable way to get the time.
    let not_before = Asn1Time::from_str("20230101000000Z")?;
    builder.set_not_before(&not_before)?;
    let not_after = Asn1Time::from_str("99991231235959Z")?;
    builder.set_not_after(&not_after)?;

    // Fixed by the DICE specification.
    builder.set_version(3)?;

    // Serial number.
    let serial_number = generator
        .get_or_register_value(&tmpl.certificate.serial_number)
        .expect("cannot get value for the certificate serial number");
    let serial_number_asn1 = Asn1Integer::from_bn(&bignum_from_bigint(&serial_number))?;
    builder.set_serial_number(&serial_number_asn1)?;

    // Issuer.
    let mut issuer_name_builder = X509NameBuilder::new()?;
    for (key, value) in &tmpl.certificate.issuer {
        let value = generator.get_or_register_value(value).with_context(|| {
            format!(
                "cannot get value of key '{}' in the certificate issuer",
                key
            )
        })?;
        if *key == AttributeType::Country && value.len() > 2 {
            bail!("The country name must fit on two characters");
        }
        issuer_name_builder.append_entry_by_nid(key.nid(), &value)?;
    }
    let issuer_name = issuer_name_builder.build();
    builder.set_issuer_name(&issuer_name)?;

    // Subject.
    let mut subject_builder = X509NameBuilder::new()?;
    for (key, value) in &tmpl.certificate.subject {
        let value = generator.get_or_register_value(value).with_context(|| {
            format!(
                "cannot get value of key '{}' in the certificate subject",
                key
            )
        })?;
        if *key == AttributeType::Country && value.len() > 2 {
            bail!("The country name must fit on two characters");
        }
        subject_builder.append_entry_by_nid(key.nid(), &value)?;
    }
    let subject = subject_builder.build();
    builder.set_subject_name(&subject)?;

    // From the Open Profile for DICE specification:
    // https://pigweed.googlesource.com/open-dice/+/refs/heads/main/docs/specification.md#certificate-details
    // The standard extensions are fixed by the specification.
    builder.append_extension(
        openssl_ext::BasicConstraints::new()
            .critical()
            .ca()
            .build()?,
    )?;

    builder.append_extension(
        openssl_ext::KeyUsage::new()
            .critical()
            .key_cert_sign()
            .build()?,
    )?;

    // The rust openssl binding does not allow to choose the subject key ID
    // and always defaults to the "hash" method of the standard. We need to use
    // raw ASN1 to work around this.
    let subject_key_id = generator
        .get_or_register_value(&tmpl.certificate.subject_key_identifier)
        .context("cannot get value for the certificate subject key ID")?;
    builder.append_extension(extension::subject_key_id_extension(&subject_key_id)?)?;

    // Openssl does not support creating an auth key identifier extension without a CA
    // or without some low-level fiddling. We need to use raw ASN1 for that.
    let auth_key_identifier =
        generator.get_or_register_value(&tmpl.certificate.authority_key_identifier)?;
    builder.append_extension(extension::auth_key_id_extension(&auth_key_identifier)?)?;

    // Collect firmware IDs.
    let fwids_digests: Vec<Vec<u8>> = tmpl
        .certificate
        .fw_ids
        .as_ref()
        .unwrap_or(&vec![])
        .iter()
        .enumerate()
        .map(|(i, fwid)| {
            let digest = generator
                .get_or_register_value(&fwid.digest)
                .with_context(|| {
                    format!("cannot get value for the certificate fw_id entry {}", i + 1)
                })?;
            if digest.len() != fwid.hash_algorithm.digest_size() {
                bail!(
                    "hash algorithm {:?} has digest size {} but the specified digest has size {}",
                    fwid.hash_algorithm,
                    fwid.hash_algorithm.digest_size(),
                    digest.len()
                );
            }
            Ok(digest)
        })
        .collect::<Result<Vec<_>>>()?;

    let fwids = tmpl.certificate.fw_ids.as_ref().map(|fw_ids| {
        let mut fwids = Vec::new();
        for (i, fwid) in fw_ids.iter().enumerate() {
            fwids.push(extension::Fwid {
                hash_alg: fwid.hash_algorithm.oid(),
                digest: &fwids_digests[i],
            });
        }
        fwids
    });

    // DICE TcbInfo
    let vendor = tmpl
        .certificate
        .vendor
        .as_ref()
        .map(|vendor| {
            generator
                .get_or_register_value(vendor)
                .context("cannot get value for the certificate DICE vendor")
        })
        .transpose()?;
    let model = tmpl
        .certificate
        .model
        .as_ref()
        .map(|model| {
            generator
                .get_or_register_value(model)
                .context("cannot get value for the certificate DICE model")
        })
        .transpose()?;
    let version = tmpl
        .certificate
        .version
        .as_ref()
        .map(|ver| {
            generator
                .get_or_register_value(ver)
                .context("cannot get value for the certificate DICE version")
        })
        .transpose()?;
    let svn = tmpl
        .certificate
        .svn
        .as_ref()
        .map(|svn| {
            generator
                .get_or_register_value(svn)
                .context("cannot get value for the certificate DICE svn")
        })
        .transpose()?
        .as_ref()
        .map(extension::Asn1OwnedBigInt::from_biguint);
    let layer = tmpl
        .certificate
        .layer
        .as_ref()
        .map(|layer| {
            generator
                .get_or_register_value(layer)
                .context("cannot get value for the certificate DICE svn")
        })
        .transpose()?
        .as_ref()
        .map(extension::Asn1OwnedBigInt::from_biguint);
    let dice_tcb_info = extension::DiceTcbInfo {
        vendor: vendor.as_deref().map(asn1::Utf8String::new),
        model: model.as_deref().map(asn1::Utf8String::new),
        version: version.as_deref().map(asn1::Utf8String::new),
        svn: svn.as_ref().map(extension::Asn1OwnedBigInt::to_asn1_bigint),
        index: None,
        layer: layer
            .as_ref()
            .map(extension::Asn1OwnedBigInt::to_asn1_bigint),
        fwids: fwids
            .as_deref()
            .map(asn1::SequenceOfWriter::new)
            .map(extension::Asn1ReadableOrWritable::new_write),
        flags: tmpl.certificate.flags,
        vendor_info: None,
        tcb_type: None,
    };
    builder.append_extension(extension::dice_tcb_info_extension(&dice_tcb_info)?)?;

    // Get the public key specified in the template or generate a random one.
    // OpenSSL will not allow us to produce an unsigned certificate so if the
    // template does not specify a public key, we have to generate a random one
    // to be able to please openssl and then find the offsets in the DER.
    let pubkey = get_or_register_pubkey(&mut generator, &tmpl.certificate.subject_public_key_info)?;
    builder.set_pubkey(&pubkey)?;

    // Sign the certificate with a public key.
    let algo = generate_signature_keypair(&tmpl.certificate.signature)?;
    builder.sign(&algo.key_pair, algo.hash)?;

    let x509 = builder.build();

    // At this point, we need to find out the value of the signature so
    // we can get the offset. This is made difficult by the fact that
    // the signature is a bit string that itself contains a DER-encoded
    // algorithm-specific structure.
    let signature = x509.signature();
    extract_and_register_signature(
        &mut generator,
        &tmpl.certificate.signature,
        signature.as_slice(),
    )?;

    let der = x509.to_der()?;
    generator.generate(tmpl.name.clone(), der, clear_fields)
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
            .unwrap_read()
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
