// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module defines substitution data that can be used to replace the
//! variables in a template by actual values.

use anyhow::{bail, ensure, Context, Result};
use hex::{FromHex, ToHex};
use num_bigint_dig::BigUint;
use num_traits::{FromPrimitive, Num};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::template::{
    Certificate, Conversion, EcPublicKey, EcPublicKeyInfo, EcdsaSignature, FirmwareId, Flags,
    Signature, SubjectPublicKeyInfo, Template, Value, Variable, VariableType,
};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(untagged)]
pub enum SubstValue {
    ByteArray(Vec<u8>),
    Int32(i32),
    String(String),
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SubstData {
    #[serde(flatten)]
    pub values: HashMap<String, SubstValue>,
}

impl Default for SubstData {
    fn default() -> Self {
        Self::new()
    }
}

impl SubstData {
    pub fn new() -> SubstData {
        SubstData {
            values: HashMap::new(),
        }
    }

    pub fn to_json(&self) -> Result<String> {
        Ok(serde_json::to_string(&self)?)
    }

    pub fn from_json(content: &str) -> Result<SubstData> {
        Ok(serde_json::from_str(content)?)
    }
}

pub trait Subst: Sized {
    fn subst(&self, data: &SubstData) -> Result<Self>;
}

impl SubstValue {
    // Parse the content of the data according to a specified
    // type. This parsing needs to be consistent with the one
    // in the template and template::hjson. See also Template::subst.
    pub fn parse(&self, var_type: &VariableType) -> Result<SubstValue> {
        match *var_type {
            VariableType::ByteArray { size } => self.parse_as_byte_array(size),
            VariableType::Integer { size } => self.parse_as_integer(size),
            VariableType::String { size } => self.parse_as_string(size),
        }
    }

    fn parse_as_byte_array(&self, size: usize) -> Result<SubstValue> {
        match self {
            SubstValue::ByteArray(bytes) => {
                ensure!(
                    bytes.len() == size,
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
                    bytes.len() == size,
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
                    bytes.len() <= size,
                    "expected an integer that fits on {size} bytes but it uses {} bytes",
                    bytes.len()
                );
                Ok(self.clone())
            }
            SubstValue::String(s) => {
                // To be consistent with the template, interpret this as
                // an integer and convert it to a big-endian byte array.
                // See template::hjson::BigUintVisitor.

                // Unless the string starts with '0x', expect a decimal string.
                let (radix, s) = s
                    .strip_prefix("0x")
                    .map_or_else(|| (10, s.as_str()), |s| (16, s));
                let val = BigUint::from_str_radix(s, radix)
                    .with_context(|| format!("cannot parse {s} as an integer"))?;
                let bytes = val.to_bytes_be();
                ensure!(
                    bytes.len() <= size,
                    "expected an integer that fits on {size} bytes but it uses {} bytes",
                    bytes.len()
                );
                Ok(SubstValue::ByteArray(bytes))
            }
            SubstValue::Int32(_) => {
                // TODO: make this check smarter (ie 0xff could fit on byte but is considered to use 4)
                ensure!(
                    4 <= size,
                    "expected an integer that fits on {size} bytes but it uses 4 bytes"
                );
                Ok(self.clone())
            }
        }
    }

    fn parse_as_string(&self, size: usize) -> Result<SubstValue> {
        match self {
            SubstValue::String(s) => {
                ensure!(
                    s.len() <= size,
                    "expected a string of at most {size} bytes but it uses {} bytes",
                    s.len()
                );
                Ok(self.clone())
            }
            _ => bail!("cannot parse value {self:?} as a string"),
        }
    }
}

impl Subst for Template {
    // Substitute data into the template. Variables that are not
    // specified in the data are left untouched. The substitution
    // will take into account the type specified in the template
    // variables. Consider an example where the substitution data
    // specifies:
    //   "x": String("3256")
    // If the template specifies:
    //   x: { type: "integer" }
    // Then "3256" will be parsed as integer 3256. On the other hand,
    // if the template specifies:
    //   x: { type: "byte-array" }
    // Then "3256" will be parsed as an hexstring and represent [0x32, 0x56].
    // This behaviour is consistent with how the data is interpreted
    // in the template hson.
    // This function will return if a substitution does not make sense (wrong type
    // or impossible conversion).
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

// This is a private trait to factor the implementation of
// Subst for Value<T>.
trait ConvertValue<T> {
    fn convert(&self, convert: &Option<Conversion>) -> Result<Value<T>>;
}

impl ConvertValue<Vec<u8>> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<Value<Vec<u8>>> {
        // The only supported conversion to byte array is from a byte array.
        let SubstValue::ByteArray(bytes) = &self else {
            bail!("cannot substitute a byte-array field with value {:?}", self);
        };
        ensure!(convert.is_none(), "substitution of a byte-array field with a byte-array value cannot specify a conversion");
        Ok(Value::Literal(bytes.clone()))
    }
}

impl ConvertValue<BigUint> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<Value<BigUint>> {
        match self {
            SubstValue::Int32(x) => {
                // No conversion supported.
                ensure!(convert.is_none(), "substitution of an integer field with an int32 value cannot specify a conversion");
                Ok(Value::Literal(
                    BigUint::from_i32(*x).expect("cannot create a BigUint from an int32"),
                ))
            }
            SubstValue::ByteArray(bytes) => {
                // No conversion means big-endian.
                match convert {
                    None | Some(Conversion::BigEndian) => {
                        Ok(Value::Literal(BigUint::from_bytes_be(&bytes)))
                    }
                    _ => bail!("substitution of an integer field with a byte-array cannot specify conversion {:?}", convert)
                }
            }
            _ => bail!("cannot substitute an integer field with value {:?}", self),
        }
    }
}

impl ConvertValue<String> for SubstValue {
    fn convert(&self, convert: &Option<Conversion>) -> Result<Value<String>> {
        match self {
            SubstValue::String(x) => {
                // No conversion supposed.
                ensure!(convert.is_none(), "substitution of a string field with a string value cannot specify a conversion");
                Ok(Value::Literal(x.clone()))
            },
            SubstValue::ByteArray(bytes) => {
                match convert {
                    Some(Conversion::LowercaseHex) => {
                        Ok(Value::Literal(bytes.encode_hex::<String>()))
                    }
                    _ => bail!("substitution of a string field with a byte-array cannot specify conversion {:?}", convert)
                }
            }
            _ => bail!("cannot substitute an string field with value {:?}", self),
        }
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
                Some(val) => val.convert(convert),
            },
        }
    }
}

impl Subst for Certificate {
    fn subst(&self, data: &SubstData) -> Result<Certificate> {
        Ok(Certificate {
            serial_number: self.serial_number.subst(data)?,
            issuer: self.issuer.subst(data)?,
            subject: self.subject.subst(data)?,
            subject_public_key_info: self.subject_public_key_info.subst(data)?,
            authority_key_identifier: self.authority_key_identifier.subst(data)?,
            subject_key_identifier: self.subject_key_identifier.subst(data)?,
            model: self.model.subst(data)?,
            vendor: self.vendor.subst(data)?,
            version: self.version.subst(data)?,
            svn: self.svn.subst(data)?,
            layer: self.layer.subst(data)?,
            fw_ids: self.fw_ids.subst(data)?,
            flags: self.flags.subst(data)?,
            signature: self.signature.subst(data)?,
        })
    }
}

impl Subst for FirmwareId {
    fn subst(&self, data: &SubstData) -> Result<FirmwareId> {
        Ok(FirmwareId {
            hash_algorithm: self.hash_algorithm.clone(),
            digest: self.digest.subst(data)?,
        })
    }
}

impl Subst for Flags {
    fn subst(&self, _data: &SubstData) -> Result<Flags> {
        Ok(self.clone())
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

impl<K, V> Subst for HashMap<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Subst,
{
    fn subst(&self, data: &SubstData) -> Result<HashMap<K, V>> {
        self.iter()
            .map(|(k, v)| Ok((k.clone(), v.subst(data)?)))
            .collect::<Result<HashMap<K, V>>>()
    }
}
