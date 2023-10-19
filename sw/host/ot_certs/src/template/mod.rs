// Copyright lowRISC contributors.
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
use num_bigint_dig::BigUint;
use serde::{Deserialize, Deserializer};
use serde_with::{serde_as, As, DeserializeAs, Same};
use std::collections::HashMap;

mod hjson;

/// Full template file, including variable declarations and certificate spec.
#[serde_as]
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct Template {
    /// Name of the certificate.
    pub name: String,
    /// Variable declarations.
    pub variables: HashMap<String, VariableType>,
    /// Certificate specification.
    pub certificate: Certificate,
}

/// Certificate specification.
#[serde_as]
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct Certificate {
    /// X509 certificate's serial number
    #[serde_as(as = "Value<hjson::BigUint>")]
    pub serial_number: Value<BigUint>,
    /// X509 certificate's issuer.
    pub issuer: HashMap<AttributeType, Value<String>>,
    /// X509 certificate's subject.
    pub subject: HashMap<AttributeType, Value<String>>,
    /// X509 certificate's public key.
    pub subject_public_key_info: SubjectPublicKeyInfo,
    /// X509 certificate's authority key identifier.
    #[serde_as(as = "Value<hjson::HexString>")]
    pub authority_key_identifier: Value<Vec<u8>>,
    /// X509 certificate's public key identifier.
    #[serde_as(as = "Value<hjson::HexString>")]
    pub subject_key_identifier: Value<Vec<u8>>,
    /// DICE TCB model.
    pub model: Option<Value<String>>,
    /// DICE TCB vendor.
    pub vendor: Option<Value<String>>,
    /// DICE TCB version.
    pub version: Option<Value<String>>,
    /// DICE TCB security version number.
    #[serde_as(as = "Option<Value<hjson::BigUint>>")]
    pub svn: Option<Value<BigUint>>,
    /// DICE TCB layer.
    #[serde_as(as = "Option<Value<hjson::BigUint>>")]
    pub layer: Option<Value<BigUint>>,
    /// DICE TCB firmware IDs.
    pub fw_ids: Option<Vec<FirmwareId>>,
    /// DICE TCB flags.
    pub flags: Option<Flags>,
    /// X509 certificate's signature.
    pub signature: Signature,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Hash, strum::Display)]
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
}

/// Value which may either be a variable name or literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value<T> {
    /// This value will be populated on the device when variables are set.
    Variable {
        /// Name of the variable.
        var: String,
        /// Optional conversion to apply to the variable.
        convert: Option<Conversion>,
    },
    /// Constant literal that will be set when the certificate is generated.
    Literal(T),
}

impl<T> Value<T> {
    /// Create a variable with the given name. No conversion applied.
    pub fn variable(name: &str) -> Self {
        Value::Variable {
            var: name.into(),
            convert: None,
        }
    }

    /// Create a variable with the given name and conversion.
    pub fn convert(var: &str, conversion: Conversion) -> Self {
        Value::Variable {
            var: var.into(),
            convert: Some(conversion),
        }
    }

    /// Create a literal with the given value.
    pub fn literal(value: impl Into<T>) -> Self {
        Value::Literal(value.into())
    }

    /// Return true if the value is a literal
    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(_))
    }
}

// Manual implementation of the deserializer since error messages for untagged
// enumerations are really terrible.
impl<'de, T, U> DeserializeAs<'de, Value<T>> for Value<U>
where
    U: DeserializeAs<'de, T> + hjson::DeserializeAsHelpMsg<T>,
{
    fn deserialize_as<D>(deserializer: D) -> Result<Value<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        // This is a horrible hack: we redefine a local type where T is now instantiated
        // and we derive a derserializer using serde but using serde with to override the
        // deserialize for T so that we can combine with SerializeAs. Since this is a local
        // type with outer generic types, we need to specify them in the type definition,
        // but U is not used so we need a phantom data to appease the compiler. We further
        // need to recall serde that there is a type bound on U.
        //
        // FIXME: this works but the error message of serde is still terrible. It might be worth
        // trying to replacing this with serde_as::PickFirst but this requires more boiler plate.
        #[derive(Deserialize)]
        #[serde(bound = "U: DeserializeAs<'de, T> + hjson::DeserializeAsHelpMsg<T>")]
        #[serde(untagged)]
        pub enum LocalValue<U, T> {
            Variable {
                var: String,
                convert: Option<Conversion>,
                #[serde(skip)]
                _phantom: std::marker::PhantomData<U>,
            },
            #[serde(with = "As::<U>")]
            Literal(T),
        }
        match LocalValue::<U, T>::deserialize(deserializer) {
            Ok(val) => match val {
                LocalValue::Literal(x) => Ok(Value::<T>::Literal(x)),
                LocalValue::Variable { var, convert, .. } => {
                    Ok(Value::<T>::Variable { var, convert })
                }
            },
            Err(_) => {
                let msg = format!("could not parse value: expected either {} or a variable (use the syntax {{var: \"name\"}}",
                                  U::help_msg());
                let example = format!("for example: {}, or {{var: \"my_variabla\"}}", U::example());
                Err(serde::de::Error::custom(format!("{}\n{}", msg, example)))
            }
        }
    }
}

// Convenience implementation to avoid using
// `serde_as(as = "Same<_>)` everywhere.
impl<'de, T> Deserialize<'de> for Value<T>
where
    T: Deserialize<'de> + hjson::DeserializeAsHelpMsg<T>,
{
    fn deserialize<D>(deserializer: D) -> Result<Value<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        As::<Value<Same>>::deserialize(deserializer)
    }
}

/// Conversion to apply to a variable when inserting it into the certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Conversion {
    /// Lower case hex: convert a byte array to a string in lowercase
    /// hexadecimal form. Every byte is printed using exactly two characters
    /// and there is no "0x" prefix. Example:
    /// [42, 53] -> "2a35".
    LowercaseHex,
    /// Little endian: convert between a byte array and integer in little endian.
    LittleEndian,
    /// Little endian: convert between a byte array and integer in little endian.
    BigEndian,
}

/// Representation of the signature of the certificate.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(tag = "algorithm", rename_all = "kebab-case")]
pub enum Signature {
    EcdsaWithSha256 { value: Option<EcdsaSignature> },
}

/// Representation of an ECDSA signature.
///
/// The signature consists of two integers "r" and "s".
/// See X9.62
#[serde_as]
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct EcdsaSignature {
    #[serde_as(as = "Value<hjson::BigUint>")]
    pub r: Value<BigUint>,
    #[serde_as(as = "Value<hjson::BigUint>")]
    pub s: Value<BigUint>,
}

/// Representation of the `SubjectPublicKeyInfo` field.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(tag = "algorithm", rename_all = "kebab-case")]
pub enum SubjectPublicKeyInfo {
    EcPublicKey(EcPublicKeyInfo),
}

/// Representation of an elliptic curve public key information.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct EcPublicKeyInfo {
    pub curve: EcCurve,
    pub public_key: EcPublicKey,
}

/// Representation of an elliptic curve public key in uncompressed
/// form.
#[serde_as]
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct EcPublicKey {
    #[serde_as(as = "Value<hjson::BigUint>")]
    pub x: Value<BigUint>,
    #[serde_as(as = "Value<hjson::BigUint>")]
    pub y: Value<BigUint>,
}

/// List of EC named curves.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub enum EcCurve {
    #[serde(rename = "prime256v1")]
    Prime256v1,
}

/// Flags that can be set for a certificate.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Deserialize)]
pub struct Flags {
    pub not_configured: bool,
    pub not_secure: bool,
    pub recovery: bool,
    pub debug: bool,
}

/// Firmware ID (fwid) field.
#[serde_as]
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
pub struct FirmwareId {
    /// Algorithm used for the has of the firmware.
    pub hash_algorithm: HashAlgorithm,
    /// Raw bytes of the hashed firmware.
    #[serde_as(as = "Value<hjson::HexString>")]
    pub digest: Value<Vec<u8>>,
}

/// Possible algorithms for computing hashes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
pub enum HashAlgorithm {
    #[serde(rename = "sha256")]
    Sha256,
}

/// Declaration of a variable that can be filled into the template.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
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
                serial_number: { var: "owner_pub_key_id", convert: "little-endian" },
                issuer: {
                  serial_number: { var: "signing_pub_key_id", convert: "lowercase-hex" },
                },
                subject: {
                  serial_number: { var: "owner_pub_key_id", convert: "lowercase-hex" },
                },
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

        let variables = HashMap::from([
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
            serial_number: Value::convert("owner_pub_key_id", Conversion::LittleEndian),
            issuer: HashMap::from([(
                AttributeType::SerialNumber,
                Value::convert("signing_pub_key_id", Conversion::LowercaseHex),
            )]),
            subject: HashMap::from([(
                AttributeType::SerialNumber,
                Value::convert("owner_pub_key_id", Conversion::LowercaseHex),
            )]),
            subject_public_key_info: SubjectPublicKeyInfo::EcPublicKey(EcPublicKeyInfo {
                curve: EcCurve::Prime256v1,
                public_key: EcPublicKey {
                    x: Value::variable("owner_pub_key_ec_x"),
                    y: Value::variable("owner_pub_key_ec_y"),
                },
            }),
            authority_key_identifier: Value::variable("signing_pub_key_id"),
            subject_key_identifier: Value::variable("owner_pub_key_id"),
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

        // Compare expected and actual parsed structs.
        let expected = Template {
            name: "cdi_owner".to_string(),
            variables,
            certificate,
        };
        let actual = Template::from_hjson_str(input).expect("failed to parse template");
        assert_eq!(expected, actual);
    }
}
