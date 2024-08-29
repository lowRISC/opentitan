// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! OpenTitan certificate template deserialization.
//!
//! This module contains structs defining certificate templates.
//!
//! These structs are defined in Hjson files and deserialized to here. Any
//! extra conversion required (beyond simple renaming) is done in the `hjson`
//! module.
//!
//! The format for a template in Hjson looks something like:
//!
//! ```hjson
//! {
//!   variables: {
//!     SomeVariableName: {
//!       type: "byte-array",
//!       size: 20,
//!     },
//!     // ...
//!   },
//!
//!   certificate: {
//!     // Certificate keys, some making use of variables, others not.
//!     serial_number: { var: "SomeVariableName" },
//!     layer: 0,
//!     // ...
//!   }
//! }
//! ```

use anyhow::Result;
use indexmap::IndexMap;
use num_bigint_dig::BigUint;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub mod subst;
pub mod testgen;

use crate::template::subst::{ConvertValue, SubstValue};

/// Full template file, including variable declarations and certificate spec.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Template {
    /// Name of the certificate.
    pub name: String,
    /// Variable declarations.
    pub variables: IndexMap<String, VariableType>,
    /// Certificate specification.
    pub certificate: Certificate,
}

/// Certificate specification.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Certificate {
    /// X509 certificate's serial number
    pub serial_number: Value<BigUint>,
    /// X509 validity's not before date. The format must be a valid ASN1 GeneralizedTime.
    pub not_before: Value<String>,
    /// X509 validity's not after date. The format must be a valid ASN1 GeneralizedTime.
    pub not_after: Value<String>,
    /// X509 certificate's issuer.
    pub issuer: Name,
    /// X509 certificate's subject.
    pub subject: Name,
    /// X509 certificate's public key.
    pub subject_public_key_info: SubjectPublicKeyInfo,
    /// X509 certificate's authority key identifier.
    pub authority_key_identifier: Value<Vec<u8>>,
    /// X509 certificate's public key identifier.
    pub subject_key_identifier: Value<Vec<u8>>,
    // X509 basic constraints extension, optional.
    pub basic_constraints: Option<BasicConstraints>,
    pub key_usage: Option<KeyUsage>,
    /// X509 Subject Alternative Name extension, optional.
    #[serde(default)]
    pub subject_alt_name: Name,
    /// Non-standard X509 certificate extensions.
    #[serde(default)]
    pub private_extensions: Vec<CertificateExtension>,
    /// X509 certificate's signature.
    pub signature: Signature,
}

/// An X501 Name (or DistinguishedName, aka DN): a DN consists of a sequence of
/// RelativeDistinguishedName (RDN). An RDN is an ordered set of attribute type
/// and value pairs. Within an RDN, each attribute type can only appear once.
/// Therefore, we represent a name as a vector of RDN, and each RDN is represented
/// by a map. The order of the vector is important: changing the order changes
/// the name. The order within the map is not important but we use an `IndexMap`
/// to make the consumers of this template use a deterministic order.
pub type Name = Vec<IndexMap<AttributeType, Value<String>>>;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct BasicConstraints {
    pub ca: Value<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct KeyUsage {
    pub digital_signature: Option<Value<bool>>,
    pub key_agreement: Option<Value<bool>>,
    pub cert_sign: Option<Value<bool>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum CertificateExtension {
    /// DICE TCB extension.
    DiceTcbInfo(DiceTcbInfoExtension),
}

/// DICE TCB extension.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct DiceTcbInfoExtension {
    /// TCB model.
    pub model: Option<Value<String>>,
    /// TCB vendor.
    pub vendor: Option<Value<String>>,
    /// TCB version.
    pub version: Option<Value<String>>,
    /// TCB security version number.
    pub svn: Option<Value<BigUint>>,
    /// TCB layer.
    pub layer: Option<Value<BigUint>>,
    /// TCB firmware IDs.
    pub fw_ids: Option<Vec<FirmwareId>>,
    /// TCB flags.
    pub flags: Option<DiceTcbInfoFlags>,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Hash, strum::Display, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AttributeType {
    #[serde(alias = "c")]
    Country,
    #[serde(alias = "o")]
    Organization,
    #[serde(alias = "ou")]
    OrganizationalUnit,
    #[serde(alias = "st")]
    State,
    #[serde(alias = "cn")]
    CommonName,
    #[serde(alias = "sn")]
    SerialNumber,
    TpmVendor,
    TpmModel,
    TpmVersion,
}

/// Value which may either be a variable name or literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value<T> {
    /// This value will be populated on the device when variables are set.
    Variable(Variable),
    /// Constant literal that will be set when the certificate is generated.
    Literal(T),
}

/// Value which may either be a variable name or literal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Variable {
    /// Name of the variable.
    pub name: String,
    /// Optional conversion to apply to the variable.
    pub convert: Option<Conversion>,
}

impl<T> Value<T> {
    /// Create a variable with the given name. No conversion applied.
    pub fn variable(name: &str) -> Self {
        Value::Variable(Variable {
            name: name.into(),
            convert: None,
        })
    }

    /// Create a variable with the given name and conversion.
    pub fn convert(var: &str, conversion: Conversion) -> Self {
        Value::Variable(Variable {
            name: var.into(),
            convert: Some(conversion),
        })
    }

    /// Create a literal with the given value.
    pub fn literal(value: impl Into<T>) -> Self {
        Value::Literal(value.into())
    }

    /// Return true if the value is a literal
    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(_))
    }

    /// Return true if this value is a variable that refers to `var_name`.
    pub fn refers_to(&self, var_name: &str) -> bool {
        match self {
            Value::Literal(_) => false,
            Value::Variable(Variable { name, .. }) => name == var_name,
        }
    }
}

// Manual implementation of the deserializer for Value<T> to call into `subst` that
// handles the parsing.
impl<'de, T> Deserialize<'de> for Value<T>
where
    T: Deserialize<'de>,
    SubstValue: ConvertValue<T>,
{
    fn deserialize<D>(deserializer: D) -> Result<Value<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(untagged)]
        pub enum LocalValue {
            Variable {
                var: String,
                convert: Option<Conversion>,
            },
            Literal(SubstValue),
        }
        match LocalValue::deserialize(deserializer) {
            Ok(val) => match val {
                LocalValue::Literal(raw_val) => {
                    let val = raw_val.convert(&None).map_err(serde::de::Error::custom)?;
                    Ok(Value::<T>::Literal(val))
                }
                LocalValue::Variable { var, convert, .. } => {
                    Ok(Value::<T>::Variable(Variable { name: var, convert }))
                }
            },
            Err(_) => {
                let msg = "could not parse value: expected either a literal (string, integer or array of bytes) or a variable (use the syntax {{var: \"name\"}}";
                Err(serde::de::Error::custom(msg))
            }
        }
    }
}

// Manual implementation of the serializer for Value<T> to call into `subst` that
// handles the serializing.
impl<T> Serialize for Value<T>
where
    SubstValue: ConvertValue<T>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[derive(Serialize)]
        #[serde(untagged)]
        pub enum LocalValue {
            Variable {
                var: String,
                convert: Option<Conversion>,
            },
            Literal(SubstValue),
        }
        let res = match self {
            Value::Variable(Variable { name, convert }) => LocalValue::Variable {
                var: name.clone(),
                convert: *convert,
            },
            Value::Literal(x) => {
                LocalValue::Literal(SubstValue::unconvert(x).map_err(serde::ser::Error::custom)?)
            }
        };
        res.serialize(serializer)
    }
}

/// Conversion to apply to a variable when inserting it into the certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Conversion {
    /// Lower case hex: convert a byte array to a string in lowercase
    /// hexadecimal form. Every byte is printed using exactly two characters
    /// and there is no "0x" prefix. Example:
    /// [42, 53] -> "2a35".
    LowercaseHex,
    /// Big endian: convert between a byte array and integer in big-endian format.
    BigEndian,
}

/// Representation of the signature of the certificate.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "algorithm", rename_all = "kebab-case")]
pub enum Signature {
    EcdsaWithSha256 { value: Option<EcdsaSignature> },
}

/// Representation of an ECDSA signature.
///
/// The signature consists of two integers "r" and "s".
/// See X9.62
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EcdsaSignature {
    pub r: Value<BigUint>,
    pub s: Value<BigUint>,
}

/// Representation of the `SubjectPublicKeyInfo` field.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "algorithm", rename_all = "kebab-case")]
pub enum SubjectPublicKeyInfo {
    EcPublicKey(EcPublicKeyInfo),
}

/// Representation of an elliptic curve public key information.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EcPublicKeyInfo {
    pub curve: EcCurve,
    pub public_key: EcPublicKey,
}

/// Representation of an elliptic curve public key in uncompressed
/// form.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct EcPublicKey {
    pub x: Value<BigUint>,
    pub y: Value<BigUint>,
}

/// List of EC named curves.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum EcCurve {
    #[serde(rename = "prime256v1")]
    Prime256v1,
}

/// Flags that can be set for a certificate.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct DiceTcbInfoFlags {
    pub not_configured: Value<bool>,
    pub not_secure: Value<bool>,
    pub recovery: Value<bool>,
    pub debug: Value<bool>,
}

/// Firmware ID (fwid) field.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct FirmwareId {
    /// Algorithm used for the has of the firmware.
    pub hash_algorithm: HashAlgorithm,
    /// Raw bytes of the hashed firmware.
    pub digest: Value<Vec<u8>>,
}

/// Possible algorithms for computing hashes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum HashAlgorithm {
    #[serde(rename = "sha256")]
    Sha256,
}

/// Declaration of a variable that can be filled into the template.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum VariableType {
    /// Raw array of bytes.
    ByteArray {
        /// Length in bytes for this variable.
        size: usize,
    },
    /// Signed integer: such an integer is represented by an array of
    /// in big-endian.
    Integer {
        /// Maximum size in bytes for this variable.
        size: usize,
    },
    /// UTF-8 encoded String.
    String {
        /// Maximum size in bytes for this variable.
        size: usize,
    },
    /// Boolean variable.
    Boolean,
}

impl Template {
    pub fn from_hjson_str(content: &str) -> Result<Template> {
        Ok(deser_hjson::from_str(content)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    /// Test parsing a typical cdi_owner template.
    #[test]
    fn cdi_owner() {
        // Input string for a Hjson template.
        let input = indoc! {r#"
            {
              name: "cdi_owner",

              variables: {
                owner_pub_key_ec_x: {
                  type: "integer",
                  size: 32,
                },
                owner_pub_key_ec_y: {
                  type: "integer",
                  size: 32,
                },
                owner_pub_key_id: {
                  type: "byte-array",
                  size: 20,
                },
                signing_pub_key_id: {
                  type: "byte-array",
                  size: 20,
                },
                rom_ext_hash: {
                  type: "byte-array",
                  size: 20,
                },
                ownership_manifest_hash: {
                  type: "byte-array",
                  size: 20,
                },
                rom_ext_security_version: {
                  type: "integer",
                  size: 4,
                }
                layer: {
                  type: "integer",
                  size: 4,
                }
                cert_signature_r: {
                  type: "integer",
                  size: 32,
                },
                cert_signature_s: {
                  type: "integer",
                  size: 32,
                },
              },

              certificate: {
                serial_number: { var: "owner_pub_key_id", convert: "big-endian" },
                issuer: [
                  { serial_number: { var: "signing_pub_key_id", convert: "lowercase-hex" } },
                ],
                not_before: "20230101000000Z",
                not_after: "99991231235959Z",
                subject: [
                  { serial_number: { var: "owner_pub_key_id", convert: "lowercase-hex" } },
                ],
                subject_public_key_info: {
                  algorithm: "ec-public-key",
                  curve: "prime256v1",
                  public_key: {
                    x: { var: "owner_pub_key_ec_x" },
                    y: { var: "owner_pub_key_ec_y" },
                  },
                },
                authority_key_identifier: { var: "signing_pub_key_id" },
                subject_key_identifier: { var: "owner_pub_key_id" },
                key_usage: { key_agreement: true },
                private_extensions: [
                    {
                        type: "dice_tcb_info",
                        vendor: "OpenTitan",
                        model: "ROM_EXT",
                        svn: { var: "rom_ext_security_version" },
                        layer: { var: "layer" },
                        version: "ES",
                        fw_ids: [
                        { hash_algorithm: "sha256", digest: { var: "rom_ext_hash" } },
                        { hash_algorithm: "sha256", digest: { var: "ownership_manifest_hash" } },
                        ],
                        flags: {
                        not_configured: true,
                        not_secure: false,
                        recovery: true,
                        debug: false,
                        }
                    },
                ],
                signature: {
                  algorithm: "ecdsa-with-sha256",
                  // The value field is optional: if not present, the signature will be cleared.
                  // Otherwise, we can reference the various fields of the signature.
                  value: {
                    r: { var: "cert_signature_r" },
                    s: { var: "cert_signature_s" }
                  }
                }
              }
            }
        "#};

        let variables = IndexMap::from([
            (
                "owner_pub_key_ec_x".to_string(),
                VariableType::Integer { size: 32 },
            ),
            (
                "owner_pub_key_ec_y".to_string(),
                VariableType::Integer { size: 32 },
            ),
            (
                "owner_pub_key_id".to_string(),
                VariableType::ByteArray { size: 20 },
            ),
            (
                "signing_pub_key_id".to_string(),
                VariableType::ByteArray { size: 20 },
            ),
            (
                "rom_ext_hash".to_string(),
                VariableType::ByteArray { size: 20 },
            ),
            (
                "ownership_manifest_hash".to_string(),
                VariableType::ByteArray { size: 20 },
            ),
            (
                "rom_ext_security_version".to_string(),
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
        ]);

        // Certificate template values.
        let certificate = Certificate {
            serial_number: Value::convert("owner_pub_key_id", Conversion::BigEndian),
            issuer: vec![IndexMap::from([(
                AttributeType::SerialNumber,
                Value::convert("signing_pub_key_id", Conversion::LowercaseHex),
            )])],
            not_before: Value::literal("20230101000000Z"),
            not_after: Value::literal("99991231235959Z"),
            subject: vec![IndexMap::from([(
                AttributeType::SerialNumber,
                Value::convert("owner_pub_key_id", Conversion::LowercaseHex),
            )])],
            subject_public_key_info: SubjectPublicKeyInfo::EcPublicKey(EcPublicKeyInfo {
                curve: EcCurve::Prime256v1,
                public_key: EcPublicKey {
                    x: Value::variable("owner_pub_key_ec_x"),
                    y: Value::variable("owner_pub_key_ec_y"),
                },
            }),
            authority_key_identifier: Value::variable("signing_pub_key_id"),
            subject_key_identifier: Value::variable("owner_pub_key_id"),
            basic_constraints: None,
            key_usage: Some(KeyUsage {
                digital_signature: None,
                key_agreement: Some(Value::literal(true)),
                cert_sign: None,
            }),
            subject_alt_name: vec![],
            private_extensions: vec![CertificateExtension::DiceTcbInfo(DiceTcbInfoExtension {
                vendor: Some(Value::literal("OpenTitan")),
                model: Some(Value::literal("ROM_EXT")),
                svn: Some(Value::variable("rom_ext_security_version")),
                layer: Some(Value::variable("layer")),
                version: Some(Value::literal("ES")),
                fw_ids: Some(Vec::from([
                    FirmwareId {
                        hash_algorithm: HashAlgorithm::Sha256,
                        digest: Value::variable("rom_ext_hash"),
                    },
                    FirmwareId {
                        hash_algorithm: HashAlgorithm::Sha256,
                        digest: Value::variable("ownership_manifest_hash"),
                    },
                ])),
                flags: Some(DiceTcbInfoFlags {
                    not_configured: Value::Literal(true),
                    not_secure: Value::Literal(false),
                    recovery: Value::Literal(true),
                    debug: Value::Literal(false),
                }),
            })],
            signature: Signature::EcdsaWithSha256 {
                value: Some(EcdsaSignature {
                    r: Value::variable("cert_signature_r"),
                    s: Value::variable("cert_signature_s"),
                }),
            },
        };

        // Compare expected and actual parsed structs.
        let expected = Template {
            name: "cdi_owner".to_string(),
            variables,
            certificate,
        };
        let actual = Template::from_hjson_str(input).expect("failed to parse template");
        // Manual assertion for pretty-printing the huge output if necessary.
        assert_eq!(
            expected, actual,
            "certificate mismatch: expected {expected:#?} but got {actual:#?}"
        );
    }
}
