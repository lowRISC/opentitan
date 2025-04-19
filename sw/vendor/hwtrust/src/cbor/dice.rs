//! Parsing and encoding DICE chain from and to CBOR.

use anyhow::Result;
use ciborium::value::Value;
use coset::iana::{self, EnumI64};
use coset::{AsCborValue, CoseKey, Label};

mod chain;
mod entry;
mod profile;

/// Type allowed for the COSE_Key object key_ops field in the DICE chain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum KeyOpsType {
    /// The key_ops field must be an array as specified in the RFC 9052.
    #[default]
    Array,
    /// The key_ops field can be either a single int or an array.
    IntOrArray,
}

/// Convert a `Value` into a `CoseKey`, respecting the `Session` options that might alter the
/// validation rules for `CoseKey`s in the DICE chain.
fn cose_key_from_cbor_value(mut value: Value, key_ops_type: KeyOpsType) -> Result<CoseKey> {
    if key_ops_type == KeyOpsType::IntOrArray {
        // Convert any integer key_ops into an array of the same integer so that the coset library
        // can handle it.
        if let Value::Map(ref mut entries) = value {
            for (label, value) in entries.iter_mut() {
                let label = Label::from_cbor_value(label.clone())?;
                if label == Label::Int(iana::KeyParameter::KeyOps.to_i64()) && value.is_integer() {
                    *value = Value::Array(vec![value.clone()]);
                }
            }
        }
    }
    Ok(CoseKey::from_cbor_value(value)?)
}
