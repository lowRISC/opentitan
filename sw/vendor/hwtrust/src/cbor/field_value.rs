//! This module defines a helper for parsing fields in a CBOR map.

use coset::{cbor::value::Value, AsCborValue, CoseEncrypt, CoseError, CoseMac0, CoseSign1};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum FieldValueError {
    #[error("expected a value for field {0}, but none was found")]
    Missing(&'static str),
    #[error("expected bytes for field {0}, but found `{1:?}`")]
    NotBytes(&'static str, Value),
    #[error("expected string for field {0}, but found `{1:?}`")]
    NotString(&'static str, Value),
    #[error("expected null for field {0}, but found `{1:?}`")]
    NotNull(&'static str, Value),
    #[error("expected u32 for field {0}, but found `{1:?}`")]
    NotU32(&'static str, Value),
    #[error("expected i64 for field {0}, but found `{1:?}`")]
    NotI64(&'static str, Value),
    #[error("expected u64 for field {0}, but found `{1:?}`")]
    NotU64(&'static str, Value),
    #[error("expected map for field {0}, but found `{1:?}`")]
    NotMap(&'static str, Value),
    #[error("expected array for field {0}, but found `{1:?}`")]
    NotArray(&'static str, Value),
    #[error("unable to parse field {0} as COSE_Sign1: `{1:?}`")]
    CoseSign1ParseError(&'static str, CoseError),
    #[error("unable to parse field {0} as COSE_Encrypt: `{1:?}`")]
    CoseEncryptParseError(&'static str, CoseError),
    #[error("unable to parse field {0} as COSE_Mac0: `{1:?}`")]
    CoseMac0ParseError(&'static str, CoseError),
    #[error("field {0} may be set only once; encountered multiple values: `{1:?}`, `{2:?}`")]
    DuplicateField(&'static str, Value, Value),
}

pub(super) struct FieldValue {
    name: &'static str,
    value: Option<Value>,
}

impl FieldValue {
    pub fn new(name: &'static str) -> Self {
        Self { name, value: None }
    }

    pub fn from_value(name: &'static str, value: Value) -> Self {
        Self { name, value: Some(value) }
    }

    pub fn from_optional_value(name: &'static str, value: Option<Value>) -> Self {
        Self { name, value }
    }

    pub fn set_once(&mut self, value: Value) -> Result<(), FieldValueError> {
        match &self.value {
            None => {
                self.value = Some(value);
                Ok(())
            }
            Some(previous) => {
                Err(FieldValueError::DuplicateField(self.name, previous.clone(), value))
            }
        }
    }

    pub fn is_bytes(&self) -> bool {
        self.value.as_ref().map_or(false, |v| v.is_bytes())
    }

    pub fn into_optional_bytes(self) -> Result<Option<Vec<u8>>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Bytes(b) => Ok(b),
                _ => Err(FieldValueError::NotBytes(self.name, v)),
            })
            .transpose()
    }

    pub fn into_bytes(self) -> Result<Vec<u8>, FieldValueError> {
        require_present(self.name, self.into_optional_bytes())
    }

    pub fn into_optional_string(self) -> Result<Option<String>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Text(s) => Ok(s),
                _ => Err(FieldValueError::NotString(self.name, v)),
            })
            .transpose()
    }

    pub fn into_string(self) -> Result<String, FieldValueError> {
        require_present(self.name, self.into_optional_string())
    }

    pub fn into_cose_encrypt(self) -> Result<CoseEncrypt, FieldValueError> {
        require_present(self.name, self.into_optional_cose_encrypt())
    }

    pub fn into_optional_cose_encrypt(self) -> Result<Option<CoseEncrypt>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Array(_) => CoseEncrypt::from_cbor_value(v)
                    .map_err(|e| FieldValueError::CoseEncryptParseError(self.name, e)),
                _ => Err(FieldValueError::NotArray(self.name, v)),
            })
            .transpose()
    }

    pub fn into_cose_mac0(self) -> Result<CoseMac0, FieldValueError> {
        require_present(self.name, self.into_optional_cose_mac0())
    }

    pub fn into_optional_cose_mac0(self) -> Result<Option<CoseMac0>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Array(_) => CoseMac0::from_cbor_value(v)
                    .map_err(|e| FieldValueError::CoseMac0ParseError(self.name, e)),
                _ => Err(FieldValueError::NotArray(self.name, v)),
            })
            .transpose()
    }

    pub fn into_cose_sign1(self) -> Result<CoseSign1, FieldValueError> {
        require_present(self.name, self.into_optional_cose_sign1())
    }

    pub fn into_optional_cose_sign1(self) -> Result<Option<CoseSign1>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Array(_) => CoseSign1::from_cbor_value(v)
                    .map_err(|e| FieldValueError::CoseSign1ParseError(self.name, e)),
                _ => Err(FieldValueError::NotArray(self.name, v)),
            })
            .transpose()
    }

    pub fn into_array(self) -> Result<Vec<Value>, FieldValueError> {
        require_present(self.name, self.into_optional_array())
    }

    pub fn into_optional_array(self) -> Result<Option<Vec<Value>>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Array(v) => Ok(v),
                _ => Err(FieldValueError::NotArray(self.name, v)),
            })
            .transpose()
    }

    pub fn into_map(self) -> Result<Vec<(Value, Value)>, FieldValueError> {
        require_present(self.name, self.into_optional_map())
    }

    pub fn into_optional_map(self) -> Result<Option<Vec<(Value, Value)>>, FieldValueError> {
        self.value
            .map(|v| match v {
                Value::Map(v) => Ok(v),
                _ => Err(FieldValueError::NotMap(self.name, v)),
            })
            .transpose()
    }

    pub fn is_null(&self) -> Result<bool, FieldValueError> {
        // If there's no value, return false; if there is a null value, return true; anything else
        // is an error.
        self.value
            .as_ref()
            .map(|v| match *v {
                Value::Null => Ok(true),
                _ => Err(FieldValueError::NotNull(self.name, v.clone())),
            })
            .unwrap_or(Ok(false))
    }

    pub fn is_integer(&self) -> bool {
        self.value.as_ref().map_or(false, |v| v.is_integer())
    }

    pub fn into_u32(self) -> Result<u32, FieldValueError> {
        require_present(self.name, self.into_optional_u32())
    }

    pub fn into_optional_u32(self) -> Result<Option<u32>, FieldValueError> {
        self.value
            .map(|v| {
                let value =
                    if let Value::Integer(i) = v { i128::from(i).try_into().ok() } else { None };
                value.ok_or(FieldValueError::NotU32(self.name, v))
            })
            .transpose()
    }

    pub fn into_optional_i64(self) -> Result<Option<i64>, FieldValueError> {
        self.value
            .map(|v| {
                let value =
                    if let Value::Integer(i) = v { i128::from(i).try_into().ok() } else { None };
                value.ok_or(FieldValueError::NotI64(self.name, v))
            })
            .transpose()
    }

    pub fn into_u64(self) -> Result<u64, FieldValueError> {
        require_present(self.name, self.into_optional_u64())
    }

    pub fn into_optional_u64(self) -> Result<Option<u64>, FieldValueError> {
        self.value
            .map(|v| {
                let value =
                    if let Value::Integer(i) = v { i128::from(i).try_into().ok() } else { None };
                value.ok_or(FieldValueError::NotU64(self.name, v))
            })
            .transpose()
    }
}

fn require_present<T>(
    name: &'static str,
    value: Result<Option<T>, FieldValueError>,
) -> Result<T, FieldValueError> {
    value.and_then(|opt| opt.ok_or(FieldValueError::Missing(name)))
}
