// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module defines substitution data that can be used to replace the
//! variables in a template by actual values.

use anyhow::{bail, ensure, Context, Result};
use hex::{FromHex, ToHex};
use indexmap::IndexMap;
use num_bigint_dig::{BigUint, ToBigInt};
use num_traits::Num;
use serde::{Deserialize, Serialize};

use crate::template::{
    BasicConstraints, Certificate, CertificateExtension, Conversion, DiceTcbInfoExtension,
    DiceTcbInfoFlags, EcPublicKey, EcPublicKeyInfo, EcdsaSignature, FirmwareId, KeyUsage,
    Signature, SubjectPublicKeyInfo, Template, Value, Variable, VariableType,
};

/// Substitution value: this is the raw value loaded from a hjson/json file
/// before any parsing.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum SubstValue {
    ByteArray(Vec<u8>),
    Int32(i32),
    String(String),
    Boolean(bool),
}

/// Substitution data for a certificate: it maps certain variables to concrete
/// values.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct SubstData {
    #[serde(flatten)]
    pub values: IndexMap<String, SubstValue>,
}

impl SubstData {
    pub fn new() -> SubstData {
        SubstData {
            values: IndexMap::new(),
        }
    }

    pub fn to_json(&self) -> Result<String> {
        Ok(serde_json::to_string(&self)?)
    }

    pub fn from_json(content: &str) -> Result<SubstData> {
        Ok(serde_json::from_str(content)?)
    }
}

/// Trait for variable substition: implement this trait to support substition
/// in data structure.
pub trait Subst: Sized {
    /// Substitute the indicated variables by their values and leave the others
    /// untouched.
    fn subst(&self, data: &SubstData) -> Result<Self>;
}

impl SubstValue {
    // Parse the content of the data according to a specified
    // type. If the type specified size is zero then any size is accepted, otherwise
    // the size constraint will be enforced.
    pub fn parse(&self, var_type: &VariableType) -> Result<SubstValue> {
        match *var_type {
            VariableType::ByteArray { size } => self.parse_as_byte_array(size),
            VariableType::Integer { size } => self.parse_as_integer(size),
            VariableType::String { size } => self.parse_as_string(size),
            VariableType::Boolean => self.parse_as_boolean(),
        }
    }

    fn parse_as_byte_array(&self, size: usize) -> Result<SubstValue> {
        match self {
            SubstValue::ByteArray(bytes) => {
                ensure!(
                    size == 0 || bytes.len() == size,
                    "expected a byte array of size {size} but got {} bytes",
                    bytes.len()
                );
                Ok(self.clone())
            }
            SubstValue::String(s) => {
                // To be consistent with the template, interpret this
                // as a hexstring.
                let bytes = Vec::<u8>::from_hex(s)
                    .with_context(|| format!("cannot parse {s} as an hexstring"))?;
                ensure!(
                    size == 0 || bytes.len() == size,
                    "expected a byte array of size {size} but got {} bytes",
                    bytes.len()
                );
                Ok(SubstValue::ByteArray(bytes))
            }
            _ => bail!("cannot parse value {self:?} as a byte-array"),
        }
    }

    fn parse_as_integer(&self, size: usize) -> Result<SubstValue> {
        match self {
            SubstValue::ByteArray(bytes) => {
                // Integer are represented as byte arrays.
                ensure!(
                    size == 0 || bytes.len() <= size,
                    "expected an integer that fits on {size} bytes but it uses {} bytes",
                    bytes.len()
                );
                Ok(self.clone())
            }
            SubstValue::String(s) => {
                // Unless the string starts with '0x', expect a decimal string.
                let (radix, s) = s
                    .strip_prefix("0x")
                    .map_or_else(|| (10, s.as_str()), |s| (16, s));
                let val = BigUint::from_str_radix(s, radix)
                    .with_context(|| format!("cannot parse {s} as an integer"))?;
                let bytes = val.to_bytes_be();
                ensure!(
                    size == 0 || bytes.len() <= size,
                    "expected an integer that fits on {size} bytes but it uses {} bytes",
                    bytes.len()
                );
                Ok(SubstValue::ByteArray(bytes))
            }
            SubstValue::Int32(x) => {
                let bigint = x.to_bigint().expect("cannot convert a i32 to BigInt");
                let bytes = bigint.to_signed_bytes_be();
                ensure!(
                    size == 0 || bytes.len() <= size,
                    "expected an integer that fits on {size} bytes but it uses 4 bytes"
                );
                Ok(SubstValue::ByteArray(bytes))
            }
            _ => bail!("cannot parse value {self:?} as an integer"),
        }
    }

    fn parse_as_string(&self, size: usize) -> Result<SubstValue> {
        match self {
            SubstValue::String(s) => {
                ensure!(
                    size == 0 || s.len() <= size,
                    "expected a string of at most {size} bytes but it uses {} bytes",
                    s.len()
                );
                Ok(self.clone())
            }
            _ => bail!("cannot parse value {self:?} as a string"),
        }
    }

    fn parse_as_boolean(&self) -> Result<SubstValue> {
        Ok(match self {
            SubstValue::Boolean(_) => self.clone(),
            SubstValue::String(s) => match s.as_str() {
                "true" => SubstValue::Boolean(true),
                "false" => SubstValue::Boolean(false),
                _ => bail!("cannot parse string '{s}' as a boolean, used either 'true' or 'false'"),
            },
            _ => bail!("cannot parse value {self:?} as a boolean"),
        })
    }
}

impl Subst for Template {
    // Substitute data into the template. Variables that are not
    // specified in the data are left untouched. Variables that appear
    /// in the data will be removed from the template's list of variables.
    // The substitution will take into account the type specified in the template
    // variables. Consider an example where the substitution data
    // specifies:
    //   "x": String("3256")
    // If the template specifies:
    //   x: { type: "integer" }
    // Then "3256" will be parsed as integer 3256. On the other hand,
    // if the template specifies:
    //   x: { type: "byte-array" }
    // Then "3256" will be parsed as an hexstring and represent [0x32, 0x56].
    // This function will return an error if a substitution does not make sense
    /// (wrong type or impossible conversion).
    fn subst(&self, data: &SubstData) -> Result<Template> {
        // The first step is to match all variables in the substitution
        // data with variables in the template to parse them if necessary.
        let mut variables = self.variables.clone();
        let mut new_data = SubstData::new();
        for (var_name, val) in data.values.iter() {
            let Some(var_type) = variables.remove(var_name) else {
                // Variable does not appear in the template: ignore it.
                continue;
            };
            new_data.values.insert(var_name.clone(), val.parse(&var_type).with_context(
                || format!("cannot parse content of substitution variable {var_name} according to the type {var_type:?} specified in the template ")
            )?);
        }
        Ok(Template {
            name: self.name.clone(),
            variables,
            certificate: self.certificate.subst(&new_data)?,
        })
    }
}

/// Trait to implement conversion from the raw (h)json data to structured data. This is used to implement variable
/// substitution in `Subst`.
pub trait ConvertValue<T>
where
    Self: Sized,
{
    /// Convert from fraw data to structured data (i.e. deserialize). Optionally provide
    /// an indication of how the data should first be parsed and how it should be converted
    /// to the type `T`.
    fn convert(&self, convert: &Option<Conversion>) -> Result<T>;
    /// Convert from structured data to raw data (i.e. serialize). The returned value shall
    /// satisfy that if then converted using `convert(None, None)` then it should return the same
    /// value.
    fn unconvert(val: &T) -> Result<Self>;
}

impl ConvertValue<Vec<u8>> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<Vec<u8>> {
        // Calling `parse` will ensure that that the returned value is a byte
        // array, this avoids duplicating code.
        let val = self.parse(&VariableType::ByteArray { size: 0 })?;
        // The only supported conversion to byte array is from a byte array.
        let SubstValue::ByteArray(bytes) = val else {
            bail!("cannot substitute a byte-array field with value {:?}", self);
        };
        ensure!(convert.is_none(), "substitution of a byte-array field with a byte-array value cannot specify a conversion");
        Ok(bytes.clone())
    }

    fn unconvert(val: &Vec<u8>) -> Result<SubstValue> {
        Ok(SubstValue::ByteArray(val.clone()))
    }
}

impl ConvertValue<BigUint> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<BigUint> {
        // Calling `parse` will ensure that that the returned value is a byte array.
        let val = self.parse(&VariableType::Integer { size: 0 })?;
        match val {
            SubstValue::ByteArray(bytes) => {
                // No conversion means big-endian.
                match convert {
                    None | Some(Conversion::BigEndian) => {
                        Ok(BigUint::from_bytes_be(&bytes))
                    }
                    _ => bail!("substitution of an integer field with a byte-array cannot specify conversion {:?}", convert)
                }
            }
            _ => bail!("cannot substitute an integer field with value {:?}", self),
        }
    }

    fn unconvert(val: &BigUint) -> Result<SubstValue> {
        // Big-endian byte array.
        Ok(SubstValue::ByteArray(val.to_bytes_be()))
    }
}

impl ConvertValue<String> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<String> {
        match self {
            SubstValue::String(x) => {
                // No conversion supported.
                ensure!(convert.is_none(), "substitution of a string field with a string value cannot specify a conversion");
                Ok(x.clone())
            },
            SubstValue::ByteArray(bytes) => {
                match convert {
                    Some(Conversion::LowercaseHex) => {
                        Ok(bytes.encode_hex::<String>())
                    }
                    _ => bail!("substitution of a string field with a byte-array cannot specify conversion {:?}", convert)
                }
            }
            _ => bail!("cannot substitute a string field with value {:?}", self),
        }
    }

    fn unconvert(val: &String) -> Result<SubstValue> {
        // Big-endian byte array.
        Ok(SubstValue::String(val.clone()))
    }
}

impl ConvertValue<bool> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<bool> {
        let SubstValue::Boolean(b) = self else {
            bail!("cannot substitute a boolean field with value {:?}", self)
        };
        // No conversion supported.
        ensure!(
            convert.is_none(),
            "substitution of a boolean field with a boolean value cannot specify a conversion"
        );
        Ok(*b)
    }

    fn unconvert(val: &bool) -> Result<SubstValue> {
        // Big-endian byte array.
        Ok(SubstValue::Boolean(*val))
    }
}

impl<T> Subst for Value<T>
where
    Value<T>: Clone,
    SubstValue: ConvertValue<T>,
{
    fn subst(&self, data: &SubstData) -> Result<Value<T>> {
        match self {
            Value::Literal(_) => Ok(self.clone()),
            Value::Variable(Variable { name, convert }) => match data.values.get(name) {
                None => Ok(self.clone()),
                Some(val) => Ok(Value::Literal(val.convert(convert)?)),
            },
        }
    }
}

impl Subst for Certificate {
    fn subst(&self, data: &SubstData) -> Result<Certificate> {
        Ok(Certificate {
            serial_number: self
                .serial_number
                .subst(data)
                .context("cannot substitute serial number")?,
            not_before: self
                .not_before
                .subst(data)
                .context("cannot substitute not_before")?,
            not_after: self
                .not_after
                .subst(data)
                .context("cannot substitute not_after")?,
            issuer: self
                .issuer
                .subst(data)
                .context("cannot substitute issuer")?,
            subject: self
                .subject
                .subst(data)
                .context("cannot substitute subject")?,
            subject_public_key_info: self
                .subject_public_key_info
                .subst(data)
                .context("cannot substitute subject public key info")?,
            authority_key_identifier: self
                .authority_key_identifier
                .subst(data)
                .context("cannot substitute authority key id")?,
            subject_key_identifier: self
                .subject_key_identifier
                .subst(data)
                .context("cannot substitute subject key id")?,
            basic_constraints: self
                .basic_constraints
                .subst(data)
                .context("cannot substitute basic constraints")?,
            key_usage: self
                .key_usage
                .subst(data)
                .context("cannot substitute key usage")?,
            private_extensions: self
                .private_extensions
                .iter()
                .map(|ext| ext.subst(data))
                .collect::<Result<Vec<_>>>()
                .context("cannot substitute in extensions")?,
            signature: self
                .signature
                .subst(data)
                .context("cannot substitute signature")?,

            subject_alt_name: self
                .subject_alt_name
                .subst(data)
                .context("cannot substitute subject alt name")?,
        })
    }
}

impl Subst for BasicConstraints {
    fn subst(&self, data: &SubstData) -> Result<BasicConstraints> {
        Ok(BasicConstraints {
            ca: self.ca.subst(data)?,
        })
    }
}

impl Subst for CertificateExtension {
    fn subst(&self, data: &SubstData) -> Result<CertificateExtension> {
        match self {
            CertificateExtension::DiceTcbInfo(dice) => Ok(CertificateExtension::DiceTcbInfo(
                dice.subst(data)
                    .context("cannot substitute in DICE extension")?,
            )),
        }
    }
}

impl Subst for DiceTcbInfoExtension {
    fn subst(&self, data: &SubstData) -> Result<DiceTcbInfoExtension> {
        Ok(DiceTcbInfoExtension {
            model: self
                .model
                .subst(data)
                .context("cannot substitute DICE model")?,
            vendor: self
                .vendor
                .subst(data)
                .context("cannot substitute DICE vendor")?,
            version: self
                .version
                .subst(data)
                .context("cannot substitute DICE version")?,
            svn: self.svn.subst(data).context("cannot substitute DICE svn")?,
            layer: self
                .layer
                .subst(data)
                .context("cannot substitute DICE layer")?,
            fw_ids: self
                .fw_ids
                .subst(data)
                .context("cannot substitute DICE firmware ids")?,
            flags: self
                .flags
                .subst(data)
                .context("cannot substitute DICE flags")?,
        })
    }
}

impl Subst for FirmwareId {
    fn subst(&self, data: &SubstData) -> Result<FirmwareId> {
        Ok(FirmwareId {
            hash_algorithm: self.hash_algorithm,
            digest: self.digest.subst(data)?,
        })
    }
}

impl Subst for DiceTcbInfoFlags {
    fn subst(&self, data: &SubstData) -> Result<DiceTcbInfoFlags> {
        Ok(DiceTcbInfoFlags {
            not_configured: self
                .not_configured
                .subst(data)
                .context("cannot substitute not_configured flag")?,
            not_secure: self
                .not_secure
                .subst(data)
                .context("cannot substitute not_configured flag")?,
            recovery: self
                .recovery
                .subst(data)
                .context("cannot substitute not_configured flag")?,
            debug: self
                .debug
                .subst(data)
                .context("cannot substitute not_configured flag")?,
        })
    }
}

impl Subst for KeyUsage {
    fn subst(&self, data: &SubstData) -> Result<KeyUsage> {
        Ok(KeyUsage {
            digital_signature: self
                .digital_signature
                .subst(data)
                .context("cannot substitute digital signature key usage")?,
            key_agreement: self
                .key_agreement
                .subst(data)
                .context("cannot substitute key agreement")?,
            cert_sign: self
                .cert_sign
                .subst(data)
                .context("cannot substitute cert sign")?,
        })
    }
}

impl Subst for SubjectPublicKeyInfo {
    fn subst(&self, data: &SubstData) -> Result<SubjectPublicKeyInfo> {
        match self {
            SubjectPublicKeyInfo::EcPublicKey(ec) => {
                Ok(SubjectPublicKeyInfo::EcPublicKey(ec.subst(data)?))
            }
        }
    }
}

impl Subst for EcPublicKeyInfo {
    fn subst(&self, data: &SubstData) -> Result<EcPublicKeyInfo> {
        Ok(EcPublicKeyInfo {
            curve: self.curve.clone(),
            public_key: self.public_key.subst(data)?,
        })
    }
}

impl Subst for EcPublicKey {
    fn subst(&self, data: &SubstData) -> Result<EcPublicKey> {
        Ok(EcPublicKey {
            x: self.x.subst(data)?,
            y: self.y.subst(data)?,
        })
    }
}

impl Subst for Signature {
    fn subst(&self, data: &SubstData) -> Result<Signature> {
        match self {
            Signature::EcdsaWithSha256 { value } => Ok(Signature::EcdsaWithSha256 {
                value: value.subst(data)?,
            }),
        }
    }
}

impl Subst for EcdsaSignature {
    fn subst(&self, data: &SubstData) -> Result<EcdsaSignature> {
        Ok(EcdsaSignature {
            r: self.r.subst(data)?,
            s: self.s.subst(data)?,
        })
    }
}

impl<T> Subst for Option<T>
where
    T: Subst,
{
    fn subst(&self, data: &SubstData) -> Result<Option<T>> {
        self.as_ref().map(|x| x.subst(data)).transpose()
    }
}

impl<T> Subst for Vec<T>
where
    T: Subst,
{
    fn subst(&self, data: &SubstData) -> Result<Vec<T>> {
        self.iter()
            .map(|x| x.subst(data))
            .collect::<Result<Vec<_>>>()
    }
}

impl<K, V> Subst for IndexMap<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Subst,
{
    fn subst(&self, data: &SubstData) -> Result<IndexMap<K, V>> {
        self.iter()
            .map(|(k, v)| Ok((k.clone(), v.subst(data)?)))
            .collect::<Result<IndexMap<K, V>>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test parsing of byte arrays.
    #[test]
    fn parse_byte_array() {
        let byte_array = SubstValue::ByteArray(vec![0xde, 0xad, 0xbe, 0xef]);
        // Size 0 means any size.
        assert_eq!(
            byte_array
                .parse(&VariableType::ByteArray { size: 0 })
                .unwrap(),
            byte_array
        );
        assert_eq!(
            byte_array
                .parse(&VariableType::ByteArray { size: 4 })
                .unwrap(),
            byte_array
        );
        assert!(byte_array
            .parse(&VariableType::ByteArray { size: 3 })
            .is_err());
        // Size must match exactly.
        assert!(byte_array
            .parse(&VariableType::ByteArray { size: 5 })
            .is_err());

        // Strings are interpreted as hexstrings.
        let byte_array_str = SubstValue::String("deadbeef".into());
        // Size 0 means any size.
        assert_eq!(
            byte_array_str
                .parse(&VariableType::ByteArray { size: 0 })
                .unwrap(),
            byte_array
        );
        assert_eq!(
            byte_array_str
                .parse(&VariableType::ByteArray { size: 4 })
                .unwrap(),
            byte_array
        );
        assert!(byte_array_str
            .parse(&VariableType::ByteArray { size: 3 })
            .is_err());
        // Size must match exactly.
        assert!(byte_array_str
            .parse(&VariableType::ByteArray { size: 5 })
            .is_err());
    }

    /// Test parsing of integers.
    #[test]
    fn parse_integers() {
        // Big-endian integer.
        let byte_array = SubstValue::ByteArray(vec![0x3f, 0x2e, 0x1d, 0x0c]);
        // Strings: hexdecimal and decimal.
        let byte_array_str_hex = SubstValue::String("0x3f2e1d0c".to_string());
        let byte_array_str_dec = SubstValue::String("1059986700".to_string());
        // Fixed-size integer.
        let byte_array_int = SubstValue::Int32(0x3f2e1d0c);

        for val in [
            &byte_array,
            &byte_array_int,
            &byte_array_str_hex,
            &byte_array_str_dec,
        ] {
            // Size 0 means any size.
            assert_eq!(
                val.parse(&VariableType::Integer { size: 0 }).unwrap(),
                byte_array
            );
            assert_eq!(
                val.parse(&VariableType::Integer { size: 4 }).unwrap(),
                byte_array
            );
            // Size does not need not match exactly.
            assert_eq!(
                val.parse(&VariableType::Integer { size: 5 }).unwrap(),
                byte_array
            );
            // Too small size in an error.
            assert!(val.parse(&VariableType::Integer { size: 3 }).is_err());
        }
    }

    /// Test parsing of strings.
    #[test]
    fn parse_strings() {
        // Big-endian integer.
        let s = SubstValue::String("OpenTitan".into());
        // Size 0 means any size.
        assert_eq!(s.parse(&VariableType::String { size: 0 }).unwrap(), s);
        assert_eq!(s.parse(&VariableType::String { size: 9 }).unwrap(), s);
        // A shorting string than specified is acceptable.
        assert_eq!(s.parse(&VariableType::String { size: 10 }).unwrap(), s);
        assert!(s.parse(&VariableType::String { size: 8 }).is_err());
    }

    /// Test parsing of booleans.
    #[test]
    fn parse_booleans() {
        for b in [false, true] {
            let b_val = SubstValue::Boolean(b);
            assert_eq!(b_val.parse(&VariableType::Boolean).unwrap(), b_val);
            let b_str = SubstValue::String(format!("{b}"));
            assert_eq!(b_str.parse(&VariableType::Boolean).unwrap(), b_val);
        }
    }

    /// Test conversion to byte arrays.
    #[test]
    fn convert_to_byte_array() {
        // Parsing is already tested so we only need to test conversion *after* parsing.

        // The only valid conversion from a byte array to a byte array is None.
        let byte_array = vec![0xde, 0xad, 0xbe, 0xef, 0x13, 0x24, 0x35];
        let array_val = SubstValue::ByteArray(byte_array.clone());
        let conv_none: Result<Vec<u8>> = array_val.convert(&None);
        let conv_lowercase: Result<Vec<u8>> = array_val.convert(&Some(Conversion::LowercaseHex));
        let conv_bigendian: Result<Vec<u8>> = array_val.convert(&Some(Conversion::BigEndian));

        assert_eq!(conv_none.unwrap(), byte_array);
        assert!(conv_lowercase.is_err());
        assert!(conv_bigendian.is_err());
        // There are no valid conversions from any other type to a byte array.
    }

    /// Test conversion to strings.
    #[test]
    fn convert_to_string() {
        // The only valid conversion from a string to a string is None.
        let s = "OpenTitan".to_string();
        let s_val = SubstValue::String(s.clone());
        let conv_none: Result<String> = s_val.convert(&None);
        let conv_lowercase: Result<String> = s_val.convert(&Some(Conversion::LowercaseHex));
        let conv_bigendian: Result<String> = s_val.convert(&Some(Conversion::BigEndian));

        assert_eq!(conv_none.unwrap(), s);
        assert!(conv_lowercase.is_err());
        assert!(conv_bigendian.is_err());

        // It is possible to convert a byte array to string (which gives the corresponding hexstring).
        // Explicitly check that the hexstring produces two characters per byte with '0' padding.
        let byte_array = vec![0x0e, 0xad, 0xbe, 0xef, 0x13, 0x24, 0x35];
        let array_hexstr = "0eadbeef132435".to_string();
        let array_val = SubstValue::ByteArray(byte_array);
        let conv_none: Result<String> = array_val.convert(&None);
        let conv_lowercase: Result<String> = array_val.convert(&Some(Conversion::LowercaseHex));
        let conv_bigendian: Result<String> = array_val.convert(&Some(Conversion::BigEndian));

        assert!(conv_none.is_err());
        assert_eq!(conv_lowercase.unwrap(), array_hexstr);
        assert!(conv_bigendian.is_err());
    }

    /// Test conversion to integers.
    #[test]
    fn convert_to_integer() {
        // Parsing is already tested so we only need to test conversion *after* parsing.

        // The only valid conversion to an integer is from a byte array using either None or big-endian.
        let byte_array = vec![0xde, 0xad, 0xbe, 0xef, 0x13, 0x24, 0x35];
        let array_val = SubstValue::ByteArray(byte_array.clone());
        let array_int = BigUint::from_bytes_be(&byte_array);
        let conv_none: Result<BigUint> = array_val.convert(&None);
        let conv_lowercase: Result<BigUint> = array_val.convert(&Some(Conversion::LowercaseHex));
        let conv_bigendian: Result<BigUint> = array_val.convert(&Some(Conversion::BigEndian));

        assert_eq!(conv_none.unwrap(), array_int);
        assert!(conv_lowercase.is_err());
        assert_eq!(conv_bigendian.unwrap(), array_int);
    }

    /// Test conversion to booleans.
    #[test]
    fn convert_to_boolean() {
        // The only valid conversion from a boolean to a boolean is None.
        let b = false;
        let b_val = SubstValue::Boolean(b);
        let conv_none: Result<bool> = b_val.convert(&None);
        let conv_lowercase: Result<bool> = b_val.convert(&Some(Conversion::LowercaseHex));
        let conv_bigendian: Result<bool> = b_val.convert(&Some(Conversion::BigEndian));

        assert_eq!(conv_none.unwrap(), b);
        assert!(conv_lowercase.is_err());
        assert!(conv_bigendian.is_err());
    }
}
