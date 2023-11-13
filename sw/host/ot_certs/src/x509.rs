// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use num_bigint_dig::BigUint;

use openssl::asn1::{Asn1Integer, Asn1Time};
use openssl::bn::{BigNum, BigNumContext};
use openssl::ec::{EcGroup, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::hash::MessageDigest;
use openssl::nid::Nid;
use openssl::pkey::PKey;
use openssl::pkey::{Private, Public};
use openssl::x509::extension as openssl_ext;
use openssl::x509::{X509NameBuilder, X509};

use crate::offsets::{CertificateWithVariables, OffsetGenerator};
use crate::template;

mod extension;
#[cfg(test)]
mod tests;

// Convert a template curve name to an openssl one.
fn ecgroup_from_curve(curve: &template::EcCurve) -> EcGroup {
    match curve {
        template::EcCurve::Prime256v1 => EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap(),
    }
}

// Represents a key pair and hash algorithm to sign the certificate.
struct KeyPairHash {
    key_pair: PKey<Private>,
    hash: MessageDigest,
}

impl KeyPairHash {
    // Generate new random ecdsa private/pub key pair.
    fn new_ecdsa_with_hash(curve: &template::EcCurve, hash: MessageDigest) -> Result<KeyPairHash> {
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
fn generate_signature_keypair(alg: &template::Signature) -> Result<KeyPairHash> {
    match alg {
        template::Signature::EcdsaWithSha256 { .. } => Ok(KeyPairHash::new_ecdsa_with_hash(
            &template::EcCurve::Prime256v1,
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
        (template::Value::Literal(x), template::Value::Literal(y)) => {
            let key = EcKey::<Public>::from_public_key_affine_coordinates(
                &group,
                &bignum_from_bigint(x),
                &bignum_from_bigint(y),
            )
            .context("could not create a public key from provided curve and x,y coordinates")?;
            Ok(PKey::try_from(key)?)
        }
        (template::Value::Variable(var_x), template::Value::Variable(var_y)) => {
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
    pubkey_info: &template::SubjectPublicKeyInfo,
) -> Result<PKey<Public>> {
    match pubkey_info {
        template::SubjectPublicKeyInfo::EcPublicKey(ec_pubkey) => {
            get_ec_pubkey(generator, ec_pubkey)
        }
    }
}

// Convert attribute types to openssl name IDs.
impl template::AttributeType {
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

// Extract the signature from an already built and signature
// certificate, and then register the signature variables with
// the generator.
fn extract_signature(
    generator: &mut OffsetGenerator,
    signature: &template::Signature,
    sigder: &[u8],
) -> Result<()> {
    match signature {
        template::Signature::EcdsaWithSha256 { value } => {
            let ecdsa_sig = EcdsaSig::from_der(sigder)
                .context("cannot extract ECDSA signature from certificate")?;
            // The ASN1 representation of r and s are as big-endian integers which is what is returned by to_vec.
            let r = ecdsa_sig.r().to_vec();
            let s = ecdsa_sig.s().to_vec();
            // If the template does not specify a value then add hidden variables to clear them.
            if let Some(value) = value {
                // We only support variables and not literals.
                let (template::Value::Variable(var_r), template::Value::Variable(var_s)) =
                    (&value.r, &value.s)
                else {
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
        if *key == template::AttributeType::Country && value.len() > 2 {
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
        if *key == template::AttributeType::Country && value.len() > 2 {
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
    extract_signature(
        &mut generator,
        &tmpl.certificate.signature,
        signature.as_slice(),
    )?;

    let der = x509.to_der()?;
    generator.generate(tmpl.name.clone(), der, clear_fields)
}
