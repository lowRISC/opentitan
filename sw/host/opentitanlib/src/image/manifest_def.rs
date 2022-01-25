// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::image::manifest::*;
use crate::util::bigint::fixed_size_bigint;
use crate::util::num_de::HexEncoded;
use crate::util::parse_int::ParseInt;

use anyhow::{anyhow, Result};
use serde::Deserialize;
use std::convert::{TryFrom, TryInto};
use std::iter::IntoIterator;

fixed_size_bigint!(ManifestRsa, 3072);

#[derive(Debug, Deserialize)]
struct ManifestBigInt(Option<HexEncoded<ManifestRsa>>);

#[derive(Debug, Deserialize)]
struct ManifestSmallInt<T: ParseInt>(Option<HexEncoded<T>>);

/// A macro for wrapping manifest struct definitions that parse from HJSON.
///
/// The #[repr(C)] version of `Manifest` can only be built when the fields in `ManifestDef` are
/// present. This macro sets up the field by field conversion and provides the field names for
/// purposes of error reporting.
macro_rules! manifest_def {
    (struct $name:ident {
        $($field_name:ident: $field_type:ty,)*
    }, $out_type:ident) => {
        #[derive(Deserialize, Debug)]
        struct $name {
            $($field_name: $field_type,)*
        }

        impl ManifestPacked<$out_type> for $name {
            fn unpack(self, _name: &'static str) -> Result<$out_type> {
                Ok($out_type {
                    // Call `unpack()` on each field with the field's name included for use in
                    // error messages.
                    $($field_name: self.$field_name
                        .unpack(stringify!($field_name))?.try_into()?,)*
                })
            }
        }
    }
}

trait ManifestPacked<T> {
    /// The default error for missing fields.
    fn unpack_err(&self, name: &'static str) -> Result<T> {
        Err(anyhow!("Manifest is missing field {}", name))
    }

    /// Unpack optional fields in the manifest, and error if the field isn't defined.
    fn unpack(self, name: &'static str) -> Result<T>;
}

impl ManifestPacked<ManifestRsa> for ManifestBigInt {
    fn unpack(self, name: &'static str) -> Result<ManifestRsa> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }
}

impl<T: ParseInt> ManifestPacked<T> for ManifestSmallInt<T> {
    fn unpack(self, name: &'static str) -> Result<T> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }
}

impl<T: ParseInt, const N: usize> ManifestPacked<[T; N]> for [ManifestSmallInt<T>; N] {
    fn unpack(self, name: &'static str) -> Result<[T; N]> {
        let results = self.map(|e| e.unpack(name));
        if let Some(err_idx) = results.iter().position(Result::is_err) {
            match IntoIterator::into_iter(results).nth(err_idx).unwrap()? {
                _ => unreachable!(),
            }
        } else {
            Ok(results.map(|x| x.unwrap()))
        }
    }
}

manifest_def! {
    struct ManifestDef {
        signature: ManifestBigInt,
        usage_constraints: ManifestUsageConstraintsDef,
        modulus: ManifestBigInt,
        exponent: ManifestSmallInt<u32>,
        identifier: ManifestSmallInt<u32>,
        length: ManifestSmallInt<u32>,
        version_major: ManifestSmallInt<u32>,
        version_minor: ManifestSmallInt<u32>,
        security_version: ManifestSmallInt<u32>,
        timestamp: ManifestSmallInt<u64>,
        binding_value: [ManifestSmallInt<u32>; 8],
        max_key_version: ManifestSmallInt<u32>,
        code_start: ManifestSmallInt<u32>,
        code_end: ManifestSmallInt<u32>,
        entry_point: ManifestSmallInt<u32>,
    }, Manifest
}

manifest_def! {
    struct ManifestUsageConstraintsDef {
        selector_bits: ManifestSmallInt<u32>,
        device_id: [ManifestSmallInt<u32>; 8],
        manuf_state_creator: ManifestSmallInt<u32>,
        manuf_state_owner: ManifestSmallInt<u32>,
        life_cycle_state: ManifestSmallInt<u32>,
    }, ManifestUsageConstraints
}

impl TryFrom<ManifestRsa> for SigverifyRsaBuffer {
    type Error = anyhow::Error;

    fn try_from(rsa: ManifestRsa) -> Result<SigverifyRsaBuffer> {
        // Convert between the BigInt byte representation and the manifest word representation.
        Ok(SigverifyRsaBuffer {
            data: rsa
                .to_le_bytes()
                .chunks(4)
                .map(|v| Ok(u32::from_le_bytes(v.try_into()?)))
                .collect::<Result<Vec<u32>>>()?
                .as_slice()
                .try_into()?,
        })
    }
}

impl TryFrom<[u32; 96]> for SigverifyRsaBuffer {
    type Error = anyhow::Error;

    fn try_from(words: [u32; 96]) -> Result<SigverifyRsaBuffer> {
        Ok(SigverifyRsaBuffer { data: words })
    }
}

impl TryFrom<[u32; 8]> for KeymgrBindingValue {
    type Error = anyhow::Error;

    fn try_from(words: [u32; 8]) -> Result<KeymgrBindingValue> {
        Ok(KeymgrBindingValue { data: words })
    }
}

impl TryFrom<[u32; 8]> for LifecycleDeviceId {
    type Error = anyhow::Error;

    fn try_from(words: [u32; 8]) -> Result<LifecycleDeviceId> {
        Ok(LifecycleDeviceId { device_id: words })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;
    use deser_hjson::from_str;

    #[test]
    fn test_manifest_from_hjson() {
        let def: ManifestDef = from_str(
            &std::fs::read_to_string(testdata!("manifest.hjson"))
                .unwrap(),
        )
        .unwrap();

        let _: Manifest = def.unpack("").unwrap();
    }
}
