//! Handling for data represented as CBOR. Cryptographic objects are encoded following COSE.

mod dice;
mod field_value;
mod publickey;
pub(crate) mod rkp;

use ciborium::value::CanonicalValue;
use ciborium::{de::from_reader, value::Value};
use std::collections::BTreeMap;
use std::io::Read;

type CiboriumError = ciborium::de::Error<std::io::Error>;

/// Decodes the provided binary CBOR-encoded value and returns a
/// ciborium::Value struct wrapped in Result.
fn value_from_bytes(mut bytes: &[u8]) -> Result<Value, CiboriumError> {
    let value = from_reader(bytes.by_ref())?;
    // Ciborium tries to read one Value, but doesn't care if there is trailing data. We do.
    if !bytes.is_empty() {
        return Err(CiboriumError::Semantic(Some(0), "unexpected trailing data".to_string()));
    }
    Ok(value)
}

fn serialize(value: Value) -> Vec<u8> {
    let mut data = Vec::new();
    ciborium::ser::into_writer(&value, &mut data).unwrap();
    data
}

fn canonicalize_map(value: Value) -> Result<Vec<u8>, CiboriumError> {
    match value {
        Value::Map(map) => {
            let btree: BTreeMap<CanonicalValue, Value> =
                map.into_iter().map(|(k, v)| (CanonicalValue::from(k), v)).collect();

            let mut data = Vec::new();
            ciborium::ser::into_writer(&btree, &mut data).unwrap();
            Ok(data)
        }
        _ => Err(CiboriumError::Semantic(None, format!("expected map, got {:?}", &value))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;

    #[test]
    fn value_from_bytes_valid_succeeds() -> Result<()> {
        let bytes = [0x82, 0x04, 0x02]; // [4, 2]
        let val = value_from_bytes(&bytes)?;
        let array = val.as_array().unwrap();
        assert_eq!(array.len(), 2);
        Ok(())
    }

    #[test]
    fn value_from_bytes_truncated_fails() {
        let bytes = [0x82, 0x04];
        assert!(value_from_bytes(&bytes).is_err());
    }

    #[test]
    fn value_from_bytes_trailing_bytes_fails() {
        let bytes = [0x82, 0x04, 0x02, 0x00];
        assert!(value_from_bytes(&bytes).is_err());
    }

    #[test]
    fn integers_and_lengths_are_canonicalized() {
        // Both are encodings of the following.
        // [1, "12", {2 : 1, 1 : 2}]
        let noncanonical_bytes = [
            0x83, // array with size 3
            0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, // integer 1
            0x7a, 0x00, 0x00, 0x00, 0x02, 0x31, 0x32, // string "12"
            0xa2, // map with size 2
            0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x01, // 2 : 1
            0x01, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, // 1 : 2
        ];
        // This is almost canonical because the keys of the map are not sorted.
        // In order to be canonical, the entries of the map should be swapped.
        let almost_canonical_bytes = [
            0x83, // array with size 3
            0x01, // integer 1
            0x62, 0x31, 0x32, // string "12"
            0xa2, // map with size 2
            0x02, 0x01, // 2 : 1
            0x01, 0x02, // 1 : 2
        ];

        let value = value_from_bytes(noncanonical_bytes.as_slice()).unwrap();
        let serialized = serialize(value);

        assert_eq!(serialized.as_slice(), almost_canonical_bytes);
    }

    #[test]
    fn canonicalization_works() {
        let bytes = [0xa2, 0x03, 0x04, 0x01, 0x02];
        let value = value_from_bytes(&bytes).unwrap();
        let canonicalized = canonicalize_map(value.clone()).unwrap();
        assert_eq!(&hex::encode(canonicalized), "a201020304");
    }
}
