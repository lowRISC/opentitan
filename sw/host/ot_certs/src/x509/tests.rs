// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use base64ct::{Base64, Encoding};
use num_bigint_dig::BigUint;
use std::collections::HashMap;

use foreign_types::{ForeignType, ForeignTypeRef};
use openssl::asn1::{Asn1IntegerRef, Asn1Object, Asn1OctetStringRef, Asn1StringRef, Asn1Time};
use openssl::ec::EcKey;
use openssl::pkey::Public;
use openssl::x509::{X509NameRef, X509};

use crate::offsets::CertificateWithVariables;
use crate::template::*;
use crate::types::Type;
use crate::x509::extension::*;
use crate::x509::*;

// Unfortunately, the rust openssl binding does not have an API to extract arbitrary extension but it exports
// the low level function from the C library to do that.
fn x509_get_ext_by_obj<'a>(x509: &'a X509, obj: &Asn1Object) -> Result<&'a Asn1OctetStringRef> {
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

#[derive(Debug)]
struct RandData {
    byte_arrays: HashMap<String, Vec<u8>>,
    strings: HashMap<String, String>,
    integers: HashMap<String, BigUint>,
}

/// Test ensuring that the offset generation is correct. Since
/// we do not know in advance the offsets, this test create a certificate
/// where every field is a variable, uses the offsets to fill those values
/// and then parse the resulting certificate using OpenSSL+asn1 to see if the values
/// match.
#[test]
fn offsets_are_correct() {
    // Generare a certificate where every field is a variable.
    let (template, mut cert_with_offsets) =
        generic_certificate().expect("could not create generic certificate");
    println!(
        "before modification: {}",
        Base64::encode_string(&cert_with_offsets.cert)
    );
    println!("{:#?}", cert_with_offsets.variables);
    // Use the offset to randomly change the variable of each variable.
    let rand_data = modify_certificate(&mut cert_with_offsets, &template);
    println!(
        "after modification: {}",
        Base64::encode_string(&cert_with_offsets.cert)
    );
    // Use OpenSSL to parse the modified certificate.
    let x509 = X509::from_der(&cert_with_offsets.cert)
        .expect("could not parse modified certificate with openssl");
    println!("{:#?}", x509);
    // Compare the values.
    compare_cert(&template, &rand_data, &x509);
}

fn extract_dice_tcb_ext(x509: &X509) -> Result<DiceTcbInfo> {
    let dice_oid =
        Asn1Object::from_str("2.23.133.5.4.1").expect("cannot create object ID from string");
    let dice_tcb_ext = x509_get_ext_by_obj(x509, &dice_oid)
        .expect("cannot extract DICE TCB extension from the certificate");
    let dice_tcb_der = dice_tcb_ext.as_slice();
    Ok(asn1::parse_single::<DiceTcbInfo>(dice_tcb_der)?)
}

fn compare_cert(template: &Template, rand: &RandData, x509: &X509) {
    assert_eq!(x509.version(), 3, "certificate has the wrong version");
    // Cannot use assert_eq! since Asn1Time does not implement Debug.
    assert!(
        x509.not_before() == Asn1Time::from_str("20230101000000Z").unwrap(),
        "certificate has the wrong validity date"
    );
    assert!(
        x509.not_after() == Asn1Time::from_str("99991231235959Z").unwrap(),
        "certificate has the wrong expiry date"
    );
    compare_names(
        "subject",
        &template.certificate.subject,
        rand,
        x509.subject_name(),
    );
    compare_names(
        "issuer",
        &template.certificate.issuer,
        rand,
        x509.issuer_name(),
    );
    compare_integer(
        "serialNumber",
        &template.certificate.serial_number,
        rand,
        x509.serial_number(),
    );
    compare_byte_array(
        "authorityKeyIdentifier",
        &template.certificate.authority_key_identifier,
        rand,
        x509.authority_key_id()
            .expect("the x509 certificate does not have an authority key identifier"),
    );
    compare_byte_array(
        "subjectKeyIdentifier",
        &template.certificate.subject_key_identifier,
        rand,
        x509.subject_key_id()
            .expect("the x509 certificate does not have an subject key identifier"),
    );
    // Extract DICE TCB extension.
    let dice_tcb = extract_dice_tcb_ext(x509).expect("Cannot parse DICE TCB extension ");
    compare_opt(
        "DICE vendor",
        &template.certificate.vendor,
        rand,
        &dice_tcb.vendor,
        compare_utf8_string,
    );
    compare_opt(
        "DICE model",
        &template.certificate.model,
        rand,
        &dice_tcb.model,
        compare_utf8_string,
    );
    compare_opt(
        "DICE version",
        &template.certificate.version,
        rand,
        &dice_tcb.version,
        compare_utf8_string,
    );
    compare_opt(
        "DICE svn",
        &template.certificate.svn,
        rand,
        &dice_tcb.svn,
        compare_bigint,
    );
    compare_opt(
        "DICE layer",
        &template.certificate.layer,
        rand,
        &dice_tcb.layer,
        compare_bigint,
    );
    compare_opt("DICE index", &None, rand, &dice_tcb.index, compare_bigint);
    assert_eq!(
        dice_tcb.index, None,
        "DICE index should not contain a value but is {:?}",
        dice_tcb.index
    );
    assert_eq!(
        template.certificate.flags, dice_tcb.flags,
        "DICE flags mismatch"
    );
    assert_eq!(
        dice_tcb.vendor_info, None,
        "DICE TCB vendor information should not contain a value but is {:?}",
        dice_tcb.index
    );
    assert_eq!(
        dice_tcb.tcb_type, None,
        "DICE TCB type information should not contain a value but is {:?}",
        dice_tcb.tcb_type
    );
    // Public key.
    let pub_key = x509
        .public_key()
        .expect("the X509 does not have a valid public key!");
    let ec_pub_key = EcKey::<Public>::try_from(pub_key).expect("the X509 is not an EC public key!");
    let mut ctx = BigNumContext::new().unwrap();
    let mut x = BigNum::new().unwrap();
    let mut y = BigNum::new().unwrap();
    ec_pub_key
        .public_key()
        .affine_coordinates(ec_pub_key.group(), &mut x, &mut y, &mut ctx)
        .unwrap();
    // Convert x and y to the DER representation, potentially adding some padding if necessary.
    let SubjectPublicKeyInfo::EcPublicKey(EcPublicKeyInfo { public_key, .. }) =
        &template.certificate.subject_public_key_info;
    compare_integer(
        "public key EC x",
        &public_key.x,
        rand,
        &x.to_asn1_integer().unwrap(),
    );
    compare_integer(
        "public key EC y",
        &public_key.y,
        rand,
        &y.to_asn1_integer().unwrap(),
    );
}

fn compare_names(
    field: &str,
    name: &HashMap<AttributeType, Value<String>>,
    rand: &RandData,
    x509_name: &X509NameRef,
) {
    println!("compare {:?} with {:?}", name, x509_name);
    assert_eq!(
        name.len(),
        x509_name.entries().count(),
        "{} field does not have the right number of entries",
        field
    );
    // Gather the nid of all entries.
    let mut unused_nids = x509_name
        .entries()
        .map(|ent| ent.object().nid())
        .collect::<std::collections::HashSet<_>>();
    for (attr, val) in name {
        let _ = unused_nids.remove(&attr.nid());
        let nid_str = attr.nid().long_name().unwrap_or("????");

        let x509_name = x509_name.to_owned().expect("cannot copy x509 name");
        let mut entries = x509_name.entries_by_nid(attr.nid());
        let entry = entries.next().unwrap_or_else(|| {
            panic!(
                "{} field has no {} entry in the X509 but got none",
                field, nid_str
            )
        });
        assert_eq!(
            entries.next().is_none(),
            true,
            "{} field has more than one {} entry in the X509",
            field,
            nid_str
        );
        compare_asn1_string(
            &format!("{} field entry {}", field, nid_str),
            val,
            rand,
            entry.data(),
        );
    }
    // Make sure that the name does not contain extra entries.
    assert!(
        unused_nids.is_empty(),
        "the X509 name contains extra entries"
    );
}

fn compare_asn1_string(field: &str, expect: &Value<String>, rand: &RandData, got: &Asn1StringRef) {
    let got = got
        .as_utf8()
        .unwrap_or_else(|err| panic!("{} is not a valid UTF-8 string: {}", field, err))
        .to_string();
    compare_str(field, expect, rand, &got);
}

fn compare_opt<T, U, F>(field: &str, expect: &Option<T>, rand: &RandData, got: &Option<U>, f: F)
where
    F: FnOnce(&str, &T, &RandData, &U),
    U: std::fmt::Debug,
{
    match (expect, got) {
        (Some(expect), Some(got)) => f(field, expect, rand, got),
        (None, None) => (),
        (Some(_), _) => panic!("{} expected a value but got none", field),
        (_, Some(_)) => panic!("{} expected no value but got one ({:?})", field, got),
    }
}

fn compare_utf8_string(
    field: &str,
    expect: &Value<String>,
    rand: &RandData,
    got: &asn1::Utf8String,
) {
    compare_str(field, expect, rand, got.as_str())
}

fn get_value<'a, T>(rand: &'a HashMap<String, T>, val: &'a Value<T>) -> &'a T {
    match val {
        Value::Variable(Variable { name, .. }) => rand
            .get(name)
            .unwrap_or_else(|| panic!("variable '{}' does not exist", name)),
        Value::Literal(s) => s,
    }
}

fn compare_str(field: &str, expect: &Value<String>, rand: &RandData, got: &str) {
    let s = get_value(&rand.strings, expect);
    assert_eq!(*s, got, "{} field does not match", field);
}

fn compare_integer(field: &str, expect: &Value<BigUint>, rand: &RandData, got: &Asn1IntegerRef) {
    let got = BigUint::from_bytes_be(
        &got.to_bn()
            .expect("cannot convert asn1 integer to bignum")
            .to_vec(),
    );
    let s = get_value(&rand.integers, expect);
    assert_eq!(*s, got, "{} field does not match", field);
}

fn compare_byte_array(
    field: &str,
    expect: &Value<Vec<u8>>,
    rand: &RandData,
    got: &Asn1OctetStringRef,
) {
    let s = get_value(&rand.byte_arrays, expect);
    assert_eq!(&**s, got.as_slice(), "{} field does not match", field);
}

fn compare_bigint(field: &str, expect: &Value<BigUint>, rand: &RandData, got: &asn1::BigInt) {
    let s = get_value(&rand.integers, expect);
    let asn1_bigint = Asn1OwnedBigInt::from_biguint(s);
    assert_eq!(
        asn1_bigint.to_asn1_bigint(),
        *got,
        "{} field does not match",
        field
    );
}

fn modify_certificate(
    cert_with_offsets: &mut CertificateWithVariables,
    tmpl: &Template,
) -> RandData {
    let mut byte_arrays = HashMap::<String, Vec<u8>>::new();
    let mut strings = HashMap::<String, String>::new();
    let mut integers = HashMap::<String, BigUint>::new();

    // We cannot just randomly modify the public key because the generated values will
    // then not be on the curve. Use OpenSSL to generate another random public key.
    let SubjectPublicKeyInfo::EcPublicKey(EcPublicKeyInfo { curve, public_key }) =
        &tmpl.certificate.subject_public_key_info;
    let Value::Variable(Variable { name: name_x, .. }) = &public_key.x else {
        panic!("the public key x must be a variable");
    };
    let Value::Variable(Variable { name: name_y, .. }) = &public_key.y else {
        panic!("the public key y must be a variable");
    };

    let group = ecgroup_from_curve(curve);
    let privkey = EcKey::<Private>::generate(&group).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let mut x = BigNum::new().unwrap();
    let mut y = BigNum::new().unwrap();
    privkey
        .public_key()
        .affine_coordinates(&group, &mut x, &mut y, &mut ctx)
        .unwrap();
    const EC_X_Y_SIZE: usize = 32;
    let x = x.to_vec_padded(EC_X_Y_SIZE.try_into().unwrap()).unwrap();
    let y = y.to_vec_padded(EC_X_Y_SIZE.try_into().unwrap()).unwrap();

    for var in &cert_with_offsets.variables {
        // Make sure that every variable appear exactly once.
        assert_eq!(
            var.offsets.len(),
            1,
            "variable {} expected to appear once",
            var.name
        );
        // Make sure that there is no conversion.
        let off = &var.offsets[0];
        assert_eq!(
            var.source_type, off.target_type,
            "variable {} expected to have the same source and target type",
            var.name
        );
        // Generate a random value, except for the public key.
        let bytes = if var.name == *name_x {
            // Convert x to the DER representation, potentially adding some padding if necessary.
            integers.insert(var.name.clone(), BigUint::from_bytes_be(&x));
            x.clone()
        } else if var.name == *name_y {
            // Same.
            integers.insert(var.name.clone(), BigUint::from_bytes_be(&y));
            y.clone()
        } else {
            match off.target_type {
                VariableType::ByteArray { size } => {
                    let (bytes, value) = Vec::<u8>::random_value(size);
                    byte_arrays.insert(var.name.clone(), value);
                    bytes
                }
                VariableType::String { size } => {
                    let (bytes, value) = String::random_value(size);
                    strings.insert(var.name.clone(), value);
                    bytes
                }
                VariableType::Integer { size } => {
                    let (bytes, value) = BigUint::random_value(size);
                    integers.insert(var.name.clone(), value);
                    bytes
                }
            }
        };
        // Overwrite the certificate
        assert_eq!(bytes.len(), off.target_type.size());
        cert_with_offsets.cert[off.offset..][..bytes.len()].copy_from_slice(&bytes);
    }

    RandData {
        byte_arrays,
        strings,
        integers,
    }
}

/// Create a generic certificate where every field is a variable.
fn generic_certificate() -> Result<(Template, CertificateWithVariables)> {
    let variables = HashMap::from([
        (
            "pub_key_ec_x".to_string(),
            VariableType::Integer { size: 32 },
        ),
        (
            "pub_key_ec_y".to_string(),
            VariableType::Integer { size: 32 },
        ),
        (
            "serial_number".to_string(),
            VariableType::Integer { size: 20 },
        ),
        (
            "subject_serial_number".to_string(),
            VariableType::String { size: 27 },
        ),
        ("issuer_cn".to_string(), VariableType::String { size: 16 }),
        (
            "issuer_c".to_string(),
            // OpenSSL has some internal constraint on the length of the country name which is 2.
            VariableType::String { size: 2 },
        ),
        (
            "pub_key_id".to_string(),
            VariableType::ByteArray { size: 20 },
        ),
        (
            "auth_key_id".to_string(),
            VariableType::ByteArray { size: 20 },
        ),
        ("hash_1".to_string(), VariableType::ByteArray { size: 20 }),
        ("hash_2".to_string(), VariableType::ByteArray { size: 20 }),
        (
            "security_version".to_string(),
            VariableType::Integer { size: 4 },
        ),
        ("layer".to_string(), VariableType::Integer { size: 4 }),
        (
            "cert_signature_r".to_string(),
            VariableType::Integer { size: 32 },
        ),
        (
            "cert_signature_s".to_string(),
            VariableType::Integer { size: 32 },
        ),
        ("model".to_string(), VariableType::String { size: 10 }),
        ("vendor".to_string(), VariableType::String { size: 11 }),
        ("vendor".to_string(), VariableType::String { size: 40 }),
    ]);

    // Certificate template.
    let certificate = Certificate {
        serial_number: Value::variable("serial_number"),
        subject: HashMap::from([(
            AttributeType::SerialNumber,
            Value::variable("subject_serial_number"),
        )]),
        issuer: HashMap::from([
            (AttributeType::Country, Value::variable("issuer_c")),
            (AttributeType::CommonName, Value::variable("issuer_cn")),
        ]),
        subject_public_key_info: SubjectPublicKeyInfo::EcPublicKey(EcPublicKeyInfo {
            curve: EcCurve::Prime256v1,
            public_key: EcPublicKey {
                x: Value::variable("pub_key_ec_x"),
                y: Value::variable("pub_key_ec_y"),
            },
        }),
        authority_key_identifier: Value::variable("auth_key_id"),
        subject_key_identifier: Value::variable("pub_key_id"),
        vendor: Some(Value::variable("vendor")),
        model: Some(Value::variable("model")),
        svn: Some(Value::variable("security_version")),
        layer: Some(Value::variable("layer")),
        version: Some(Value::literal("version")),
        fw_ids: Some(Vec::from([
            FirmwareId {
                hash_algorithm: HashAlgorithm::Sha256,
                digest: Value::variable("hash_1"),
            },
            FirmwareId {
                hash_algorithm: HashAlgorithm::Sha256,
                digest: Value::variable("hash_2"),
            },
        ])),
        flags: Some(Flags {
            not_configured: true,
            not_secure: false,
            recovery: true,
            debug: false,
        }),
        signature: Signature::EcdsaWithSha256 {
            value: Some(EcdsaSignature {
                r: Value::variable("cert_signature_r"),
                s: Value::variable("cert_signature_s"),
            }),
        },
    };
    let template = Template {
        name: "generic".to_string(),
        variables,
        certificate,
    };
    // Generate certificate and offsets.
    Ok((
        template.clone(),
        crate::x509::generate_certificate(&template, false)?,
    ))
}
