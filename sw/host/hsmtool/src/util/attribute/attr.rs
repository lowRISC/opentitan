// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::object::{Attribute, AttributeInfo, ObjectHandle};
use cryptoki::session::Session;
use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use strum::IntoEnumIterator;

use super::AttrData;
use super::AttributeError;
use super::AttributeType;
use super::CertificateType;
use super::Date;
use super::KeyType;
use super::MechanismType;
use super::ObjectClass;

/// Converts a cryptoki `Attribute` into a key-value pair of
/// `(AttributeType, AttrData)`.  This allows converting HSM
/// attribute lists into an easier to manipulat mapping.
fn into_kv(attr: &Attribute) -> Result<(AttributeType, AttrData)> {
    match attr {
        // CK_BBOOL
        Attribute::AlwaysAuthenticate(b)
        | Attribute::AlwaysSensitive(b)
        | Attribute::Copyable(b)
        | Attribute::Decrypt(b)
        | Attribute::Derive(b)
        | Attribute::Destroyable(b)
        | Attribute::Encrypt(b)
        | Attribute::Extractable(b)
        | Attribute::Local(b)
        | Attribute::Modifiable(b)
        | Attribute::NeverExtractable(b)
        | Attribute::Private(b)
        | Attribute::Sensitive(b)
        | Attribute::Sign(b)
        | Attribute::SignRecover(b)
        | Attribute::Token(b)
        | Attribute::Trusted(b)
        | Attribute::Unwrap(b)
        | Attribute::Verify(b)
        | Attribute::VerifyRecover(b)
        | Attribute::Wrap(b)
        | Attribute::WrapWithTrusted(b) => Ok((
            AttributeType::from(attr.attribute_type()),
            AttrData::from(*b),
        )),
        // CK_ULONG
        Attribute::ModulusBits(val) | Attribute::ValueLen(val) => Ok((
            AttributeType::from(attr.attribute_type()),
            AttrData::from(*val),
        )),
        // Vec<u8>, but ascii text
        Attribute::Application(bytes) | Attribute::Label(bytes) | Attribute::Url(bytes) => Ok((
            AttributeType::from(attr.attribute_type()),
            AttrData::from_ascii_bytes(bytes.as_slice()),
        )),
        // Vec<u8>, binary data
        Attribute::AcIssuer(bytes)
        | Attribute::AttrTypes(bytes)
        | Attribute::Base(bytes)
        | Attribute::CheckValue(bytes)
        | Attribute::Coefficient(bytes)
        | Attribute::EcParams(bytes)
        | Attribute::EcPoint(bytes)
        | Attribute::Exponent1(bytes)
        | Attribute::Exponent2(bytes)
        | Attribute::HashOfIssuerPublicKey(bytes)
        | Attribute::HashOfSubjectPublicKey(bytes)
        | Attribute::Issuer(bytes)
        | Attribute::ObjectId(bytes)
        | Attribute::Prime(bytes)
        | Attribute::Prime1(bytes)
        | Attribute::Prime2(bytes)
        | Attribute::PrivateExponent(bytes)
        | Attribute::PublicExponent(bytes)
        | Attribute::PublicKeyInfo(bytes)
        | Attribute::Modulus(bytes)
        | Attribute::Owner(bytes)
        | Attribute::SerialNumber(bytes)
        | Attribute::Subject(bytes)
        | Attribute::Value(bytes)
        | Attribute::Id(bytes) => Ok((
            AttributeType::from(attr.attribute_type()),
            AttrData::from(bytes.as_slice()),
        )),
        // Unique types
        Attribute::CertificateType(certificate_type) => {
            let val = CertificateType::from(*certificate_type);
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::from(val),
            ))
        }
        Attribute::Class(object_class) => {
            let val = ObjectClass::from(*object_class);
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::from(val),
            ))
        }
        Attribute::KeyGenMechanism(mech) => {
            let val = MechanismType::from(*mech);
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::from(val),
            ))
        }
        Attribute::KeyType(key_type) => {
            let val = KeyType::from(*key_type);
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::from(val),
            ))
        }
        Attribute::AllowedMechanisms(mechanisms) => {
            let val = mechanisms
                .iter()
                .map(|m| AttrData::from(MechanismType::from(*m)))
                .collect::<Vec<_>>();
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::List(val),
            ))
        }
        Attribute::EndDate(date) | Attribute::StartDate(date) => {
            let val = Date::from(*date);
            Ok((
                AttributeType::from(attr.attribute_type()),
                AttrData::Str(val.into()),
            ))
        }
        _ => Err(AttributeError::UnknownAttribute(attr.clone()).into()),
    }
}

/// Converts an hsmtool `(AttributeType, AttrData)` pair into a
/// cryptoki `Attribute`.  This facilitates converting a mapping of attributes
/// into an HSM-ready `Attribute`.
fn from_kv(atype: AttributeType, data: &AttrData) -> Result<Attribute> {
    match atype {
        AttributeType::AcIssuer => Ok(Attribute::AcIssuer(data.try_into()?)),
        AttributeType::AllowedMechanisms => match data {
            AttrData::List(v) => {
                let mechs = v
                    .iter()
                    .map(|a| Ok(MechanismType::try_from(a)?.try_into()?))
                    .collect::<Result<Vec<cryptoki::mechanism::MechanismType>>>()?;
                Ok(Attribute::AllowedMechanisms(mechs))
            }
            _ => Err(AttributeError::InvalidDataType.into()),
        },
        AttributeType::AlwaysAuthenticate => Ok(Attribute::AlwaysAuthenticate(data.try_into()?)),
        AttributeType::AlwaysSensitive => Ok(Attribute::AlwaysSensitive(data.try_into()?)),
        AttributeType::Application => Ok(Attribute::Application(data.try_into()?)),
        AttributeType::AttrTypes => Ok(Attribute::AttrTypes(data.try_into()?)),
        AttributeType::Base => Ok(Attribute::Base(data.try_into()?)),
        AttributeType::CertificateType => Ok(Attribute::CertificateType(
            CertificateType::try_from(data)?.try_into()?,
        )),
        AttributeType::CheckValue => Ok(Attribute::CheckValue(data.try_into()?)),
        AttributeType::Class => Ok(Attribute::Class(ObjectClass::try_from(data)?.try_into()?)),
        AttributeType::Coefficient => Ok(Attribute::Coefficient(data.try_into()?)),
        AttributeType::Copyable => Ok(Attribute::Copyable(data.try_into()?)),
        AttributeType::Decrypt => Ok(Attribute::Decrypt(data.try_into()?)),
        AttributeType::Derive => Ok(Attribute::Derive(data.try_into()?)),
        AttributeType::Destroyable => Ok(Attribute::Destroyable(data.try_into()?)),
        AttributeType::EcParams => Ok(Attribute::EcParams(data.try_into()?)),
        AttributeType::EcPoint => Ok(Attribute::EcPoint(data.try_into()?)),
        AttributeType::Encrypt => Ok(Attribute::Encrypt(data.try_into()?)),
        AttributeType::EndDate => Ok(Attribute::EndDate(Date::try_from(data)?.try_into()?)),
        AttributeType::Exponent1 => Ok(Attribute::Exponent1(data.try_into()?)),
        AttributeType::Exponent2 => Ok(Attribute::Exponent2(data.try_into()?)),
        AttributeType::Extractable => Ok(Attribute::Extractable(data.try_into()?)),
        AttributeType::HashOfIssuerPublicKey => {
            Ok(Attribute::HashOfIssuerPublicKey(data.try_into()?))
        }
        AttributeType::HashOfSubjectPublicKey => {
            Ok(Attribute::HashOfSubjectPublicKey(data.try_into()?))
        }
        AttributeType::Id => Ok(Attribute::Id(data.try_into()?)),
        AttributeType::Issuer => Ok(Attribute::Issuer(data.try_into()?)),
        AttributeType::KeyGenMechanism => Ok(Attribute::KeyGenMechanism(
            MechanismType::try_from(data)?.try_into()?,
        )),
        AttributeType::KeyType => Ok(Attribute::KeyType(KeyType::try_from(data)?.try_into()?)),
        AttributeType::Label => Ok(Attribute::Label(data.try_into()?)),
        AttributeType::Local => Ok(Attribute::Local(data.try_into()?)),
        AttributeType::Modifiable => Ok(Attribute::Modifiable(data.try_into()?)),
        AttributeType::Modulus => Ok(Attribute::Modulus(data.try_into()?)),
        AttributeType::ModulusBits => Ok(Attribute::ModulusBits(data.try_into()?)),
        AttributeType::NeverExtractable => Ok(Attribute::NeverExtractable(data.try_into()?)),
        AttributeType::ObjectId => Ok(Attribute::ObjectId(data.try_into()?)),
        AttributeType::Owner => Ok(Attribute::Owner(data.try_into()?)),
        AttributeType::Prime => Ok(Attribute::Prime(data.try_into()?)),
        AttributeType::Prime1 => Ok(Attribute::Prime1(data.try_into()?)),
        AttributeType::Prime2 => Ok(Attribute::Prime2(data.try_into()?)),
        AttributeType::Private => Ok(Attribute::Private(data.try_into()?)),
        AttributeType::PrivateExponent => Ok(Attribute::PrivateExponent(data.try_into()?)),
        AttributeType::PublicExponent => Ok(Attribute::PublicExponent(data.try_into()?)),
        AttributeType::PublicKeyInfo => Ok(Attribute::PublicKeyInfo(data.try_into()?)),
        AttributeType::Sensitive => Ok(Attribute::Sensitive(data.try_into()?)),
        AttributeType::SerialNumber => Ok(Attribute::SerialNumber(data.try_into()?)),
        AttributeType::Sign => Ok(Attribute::Sign(data.try_into()?)),
        AttributeType::SignRecover => Ok(Attribute::SignRecover(data.try_into()?)),
        AttributeType::StartDate => Ok(Attribute::StartDate(Date::try_from(data)?.try_into()?)),
        AttributeType::Subject => Ok(Attribute::Subject(data.try_into()?)),
        AttributeType::Token => Ok(Attribute::Token(data.try_into()?)),
        AttributeType::Trusted => Ok(Attribute::Trusted(data.try_into()?)),
        AttributeType::Unwrap => Ok(Attribute::Unwrap(data.try_into()?)),
        AttributeType::Url => Ok(Attribute::Url(data.try_into()?)),
        AttributeType::Value => Ok(Attribute::Value(data.try_into()?)),
        AttributeType::ValueLen => Ok(Attribute::ValueLen(data.try_into()?)),
        AttributeType::Verify => Ok(Attribute::Verify(data.try_into()?)),
        AttributeType::VerifyRecover => Ok(Attribute::VerifyRecover(data.try_into()?)),
        AttributeType::Wrap => Ok(Attribute::Wrap(data.try_into()?)),
        AttributeType::WrapWithTrusted => Ok(Attribute::WrapWithTrusted(data.try_into()?)),
        _ => Err(AttributeError::UnknownAttributeType(atype).into()),
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct AttributeMap(IndexMap<AttributeType, AttrData>);

impl From<&[Attribute]> for AttributeMap {
    fn from(a: &[Attribute]) -> Self {
        AttributeMap(
            a.iter()
                .map(|a| into_kv(a).expect("convert from attribute"))
                .collect(),
        )
    }
}

impl AttributeMap {
    /// Generates a list of all AttributeTypes known to the cryptoki library.
    /// This list can be used to retrieve all attributes of an HSM-object to
    /// faciltate showing, exporting or modifying objects.
    ///
    /// This function only generates the list of known attributes once.
    pub fn all() -> &'static [cryptoki::object::AttributeType] {
        static VALID_TYPES: OnceCell<Vec<cryptoki::object::AttributeType>> = OnceCell::new();
        VALID_TYPES
            .get_or_init(|| {
                AttributeType::iter()
                    .map(|a| Ok(a.try_into()?))
                    .filter(|a| a.is_ok())
                    .collect::<Result<Vec<_>>>()
                    .unwrap()
            })
            .as_slice()
    }

    /// Inserts a `key`/`value` pair into the mapping, returing the
    /// previous value (if any).
    pub fn insert(&mut self, key: AttributeType, value: AttrData) -> Option<AttrData> {
        self.0.insert(key, value)
    }

    /// Retrieves an `AttrData` value for the given `key`.
    pub fn get(&self, key: &AttributeType) -> Option<&AttrData> {
        self.0.get(key)
    }

    /// Returns true if the `AttributeMap` is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Converts the `AttributeMap` to a cryptoki ready list of `Attributes`.
    pub fn to_vec(&self) -> Result<Vec<Attribute>> {
        self.0.iter().map(|(k, v)| from_kv(*k, v)).collect()
    }

    /// Merges an `other` mapping into `self`.
    pub fn merge(&mut self, other: AttributeMap) {
        for (k, v) in other.0 {
            self.insert(k, v);
        }
    }

    /// Retrieves an object from the PKCS#11 interface as an `AttributeMap`.
    pub fn from_object(session: &Session, object: ObjectHandle) -> Result<Self> {
        let all = Self::all();
        let info = session.get_attribute_info(object, all)?;
        let mut atypes = Vec::new();
        for (&a, i) in all.iter().zip(info.iter()) {
            if matches!(i, AttributeInfo::Available(_)) {
                atypes.push(a);
            }
        }
        let attrs = session.get_attributes(object, &atypes)?;
        let mut map = AttributeMap::from(attrs.as_slice());
        for (&a, i) in all.iter().zip(info.iter()) {
            if matches!(i, AttributeInfo::Sensitive) {
                map.insert(a.into(), AttrData::None);
            }
        }
        Ok(map)
    }
}

impl FromStr for AttributeMap {
    type Err = anyhow::Error;

    /// Parses an `AttributeMap` from a string or file.
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        if let Some(path) = s.strip_prefix('@') {
            let data = std::fs::read_to_string(path)?;
            Ok(serde_annotate::from_str(&data)?)
        } else {
            Ok(serde_annotate::from_str(s)?)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_to_kv() -> Result<()> {
        let a = Attribute::Copyable(true);
        let (ty, data) = into_kv(&a)?;
        assert_eq!(ty, AttributeType::Copyable);
        assert_eq!(data, AttrData::Bool(true));
        Ok(())
    }

    #[test]
    fn test_kv_to_attribute() -> Result<()> {
        let a = from_kv(AttributeType::Copyable, &AttrData::Bool(true))?;
        assert!(matches!(a, Attribute::Copyable(true)));
        Ok(())
    }

    const ATTR_MAP: &str = r#"{
  "CKA_COPYABLE": true,
  "CKA_MODULUS_BITS": 3072,
  "CKA_LABEL": "foo",
  "CKA_OBJECT_ID": "12:34:56:78",
  "CKA_CERTIFICATE_TYPE": "CKC_X_509",
  "CKA_CLASS": "CKO_CERTIFICATE",
  "CKA_KEY_TYPE": "CKK_RSA",
  "CKA_KEY_GEN_MECHANISM": "CKM_RSA_PKCS",
  "CKA_ALLOWED_MECHANISMS": [
    "CKM_RSA_PKCS",
    "CKM_RSA_PKCS_KEY_PAIR_GEN"
  ],
  "CKA_START_DATE": "2023-02-15"
}"#;

    #[test]
    fn test_to_attribute_map() -> Result<()> {
        let a = [
            Attribute::Copyable(true),
            Attribute::ModulusBits(3072u64.into()),
            Attribute::Label(vec![b'f', b'o', b'o']),
            Attribute::ObjectId(vec![0x12, 0x34, 0x56, 0x78]),
            Attribute::CertificateType(CertificateType::X509.try_into()?),
            Attribute::Class(ObjectClass::Certificate.try_into()?),
            Attribute::KeyType(KeyType::Rsa.try_into()?),
            Attribute::KeyGenMechanism(MechanismType::RsaPkcs.try_into()?),
            Attribute::AllowedMechanisms(vec![
                MechanismType::RsaPkcs.try_into()?,
                MechanismType::RsaPkcsKeyPairGen.try_into()?,
            ]),
            Attribute::StartDate(Date::from("2023-02-15").try_into()?),
        ];
        let am = AttributeMap::from(a.as_slice());
        let json = serde_json::to_string_pretty(&am)?;
        assert_eq!(json, ATTR_MAP);
        Ok(())
    }

    #[test]
    fn test_from_attribute_map() -> Result<()> {
        let map = serde_json::from_str::<AttributeMap>(ATTR_MAP)?;
        let a = map.to_vec()?;
        // Currently, the best way to check that the attributes have the
        // expected values is to check the output of the Debug trait.
        let result = format!("{:x?}", a);
        assert_eq!(result, "[Copyable(true), ModulusBits(Ulong { val: c00 }), Label([66, 6f, 6f]), ObjectId([12, 34, 56, 78]), CertificateType(CertificateType { val: 0 }), Class(ObjectClass { val: 1 }), KeyType(KeyType { val: 0 }), KeyGenMechanism(MechanismType { val: 1 }), AllowedMechanisms([MechanismType { val: 1 }, MechanismType { val: 0 }]), StartDate(Date { date: _CK_DATE { year: [32, 30, 32, 33], month: [30, 32], day: [31, 35] } })]");
        Ok(())
    }
}
