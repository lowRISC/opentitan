// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::image::manifest::*;
use crate::util::bigint::fixed_size_bigint;
use crate::util::num_de::HexEncoded;
use crate::util::parse_int::ParseInt;

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::iter::IntoIterator;
use std::path::Path;
use thiserror::Error;

use zerocopy::AsBytes;

#[derive(Debug, Error)]
pub enum ManifestError {
    #[error("Manifest is missing field \"{0}\".")]
    MissingField(&'static str),
}

fixed_size_bigint!(ManifestRsaBuffer, at_most 3072);
fixed_size_bigint!(ManifestSpxSignature, at_most 62848);
fixed_size_bigint!(ManifestSpxKey, at_most 256);

#[derive(Clone, Default, Debug, Deserialize, Serialize)]
struct ManifestRsaBigInt(Option<HexEncoded<ManifestRsaBuffer>>);

#[derive(Clone, Default, Debug, Deserialize, Serialize)]
struct ManifestSpxSignatureBigInt(Option<HexEncoded<ManifestSpxSignature>>);

#[derive(Clone, Default, Debug, Deserialize, Serialize)]
struct ManifestSpxKeyBigInt(Option<HexEncoded<ManifestSpxKey>>);

#[derive(Clone, Default, Debug, Deserialize, Serialize)]
struct ManifestSmallInt<T: ParseInt + fmt::LowerHex>(Option<HexEncoded<T>>);

impl fmt::LowerHex for ManifestRsaBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::LowerHex::fmt(&self.as_biguint(), f)
    }
}

impl fmt::LowerHex for ManifestSpxSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::LowerHex::fmt(&self.as_biguint(), f)
    }
}

impl fmt::LowerHex for ManifestSpxKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::LowerHex::fmt(&self.as_biguint(), f)
    }
}

/// A macro for wrapping manifest struct definitions that parse from HJSON.
///
/// The #[repr(C)] version of `Manifest` can only be built when the fields in `ManifestSpec` are
/// present. This macro sets up the field by field conversion and provides the field names for
/// purposes of error reporting.
macro_rules! manifest_def {
    ($access:vis struct $name:ident {
        $(
            $(#[$doc:meta])?
            $field_name:ident: $field_type:ty,
        )*
    }, $out_type:ident) => {
        #[derive(Clone, Default, Deserialize, Serialize, Debug)]
        $access struct $name {
            $(
                $(#[$doc])?
                #[serde(default)]
                $field_name: $field_type,
            )*
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

            fn overwrite(&mut self, o: $name) {
                $(self.$field_name.overwrite(o.$field_name);)*
            }
        }

        impl TryInto<$out_type> for $name {
            type Error = anyhow::Error;

            fn try_into(self) -> Result<$out_type> {
                self.unpack("")
            }
        }

        impl TryFrom<&$out_type> for $name {
            type Error = anyhow::Error;

            fn try_from(o: &$out_type) -> Result<Self> {
                Ok($name {
                    $($field_name: (&o.$field_name).try_into()?,)*
                })
            }
        }
    }
}

impl ManifestSpec {
    pub fn read_from_file(path: &Path) -> Result<ManifestSpec> {
        Ok(deser_hjson::from_str(&std::fs::read_to_string(path)?)?)
    }

    pub fn overwrite_fields(&mut self, other: ManifestSpec) {
        self.overwrite(other)
    }

    pub fn update_spx_signature(&mut self, spx_signature: ManifestSpxSignature) {
        self.spx_signature.0 = Some(HexEncoded(spx_signature))
    }

    pub fn update_spx_key(&mut self, spx_key: ManifestSpxKey) {
        self.spx_key.0 = Some(HexEncoded(spx_key))
    }

    pub fn update_rsa_signature(&mut self, rsa_signature: ManifestRsaBuffer) {
        self.rsa_signature.0 = Some(HexEncoded(rsa_signature))
    }

    pub fn update_modulus(&mut self, rsa_modulus: ManifestRsaBuffer) {
        self.rsa_modulus.0 = Some(HexEncoded(rsa_modulus))
    }

    pub fn rsa_signature(&self) -> Option<&ManifestRsaBuffer> {
        self.rsa_signature.0.as_ref().map(|v| &v.0)
    }

    pub fn spx_signature(&self) -> Option<&ManifestSpxSignature> {
        self.spx_signature.0.as_ref().map(|v| &v.0)
    }

    pub fn spx_key(&self) -> Option<&ManifestSpxKey> {
        self.spx_key.0.as_ref().map(|v| &v.0)
    }

    pub fn rsa_modulus(&self) -> Option<&ManifestRsaBuffer> {
        self.rsa_modulus.0.as_ref().map(|v| &v.0)
    }
}

trait ManifestPacked<T> {
    /// The default error for missing fields.
    fn unpack_err(&self, name: &'static str) -> Result<T> {
        bail!(ManifestError::MissingField(name))
    }

    /// Unpack optional fields in the manifest, and error if the field isn't defined.
    fn unpack(self, name: &'static str) -> Result<T>;

    /// Overwrite manifest field.
    fn overwrite(&mut self, o: Self);
}

impl ManifestPacked<ManifestRsaBuffer> for ManifestRsaBigInt {
    fn unpack(self, name: &'static str) -> Result<ManifestRsaBuffer> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }

    fn overwrite(&mut self, o: Self) {
        if o.0.is_some() {
            *self = o;
        }
    }
}

impl ManifestPacked<ManifestSpxSignature> for ManifestSpxSignatureBigInt {
    fn unpack(self, name: &'static str) -> Result<ManifestSpxSignature> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }

    fn overwrite(&mut self, o: Self) {
        if o.0.is_some() {
            *self = o;
        }
    }
}

impl ManifestPacked<ManifestSpxKey> for ManifestSpxKeyBigInt {
    fn unpack(self, name: &'static str) -> Result<ManifestSpxKey> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }

    fn overwrite(&mut self, o: Self) {
        if o.0.is_some() {
            *self = o;
        }
    }
}

impl ManifestPacked<[ManifestExtTableEntry; 8]> for [ManifestExtTableEntryDef; 8] {
    fn unpack(self, _name: &'static str) -> Result<[ManifestExtTableEntry; 8]> {
        Ok(self.map(|v| ManifestExtTableEntry {
            identifier: *v.identifier.0.unwrap(),
            offset: *v.offset.0.unwrap(),
        }))
    }

    fn overwrite(&mut self, o: Self) {
        for i in 0..self.len() {
            if o[i].identifier.0.is_some() {
                self[i].identifier = o[i].identifier.clone()
            }
            if o[i].offset.0.is_some() {
                self[i].offset = o[i].offset.clone()
            }
        }
    }
}

impl<T: ParseInt + fmt::LowerHex> ManifestPacked<T> for ManifestSmallInt<T> {
    fn unpack(self, name: &'static str) -> Result<T> {
        match self.0 {
            Some(v) => Ok(v.0),
            None => self.unpack_err(name),
        }
    }

    fn overwrite(&mut self, o: Self) {
        if o.0.is_some() {
            *self = o;
        }
    }
}

impl<T: ParseInt + fmt::LowerHex, const N: usize> ManifestPacked<[T; N]>
    for [ManifestSmallInt<T>; N]
{
    fn unpack(self, name: &'static str) -> Result<[T; N]> {
        let results = self.map(|e| e.unpack(name));
        if let Some(err_idx) = results.iter().position(Result::is_err) {
            IntoIterator::into_iter(results).nth(err_idx).unwrap()?;
            unreachable!();
        } else {
            Ok(results.map(|x| x.unwrap()))
        }
    }

    fn overwrite(&mut self, o: Self) {
        // Only perform the overwrite if all elements of `o` are present.
        if o.iter().all(|v| v.0.is_some()) {
            *self = o;
        }
    }
}

manifest_def! {
    pub struct ManifestSpec {
        spx_signature: ManifestSpxSignatureBigInt,
        rsa_signature: ManifestRsaBigInt,
        usage_constraints: ManifestUsageConstraintsDef,
        spx_key: ManifestSpxKeyBigInt,
        rsa_modulus: ManifestRsaBigInt,
        address_translation: ManifestSmallInt<u32>,
        identifier: ManifestSmallInt<u32>,
        signed_region_end: ManifestSmallInt<u32>,
        length: ManifestSmallInt<u32>,
        version_major: ManifestSmallInt<u32>,
        version_minor: ManifestSmallInt<u32>,
        security_version: ManifestSmallInt<u32>,
        timestamp: [ManifestSmallInt<u32>; 2],
        binding_value: [ManifestSmallInt<u32>; 8],
        max_key_version: ManifestSmallInt<u32>,
        code_start: ManifestSmallInt<u32>,
        code_end: ManifestSmallInt<u32>,
        entry_point: ManifestSmallInt<u32>,
        extensions: [ManifestExtTableEntryDef; 8],
    }, Manifest
}

manifest_def! {
    pub struct ManifestUsageConstraintsDef {
        selector_bits: ManifestSmallInt<u32>,
        device_id: [ManifestSmallInt<u32>; 8],
        manuf_state_creator: ManifestSmallInt<u32>,
        manuf_state_owner: ManifestSmallInt<u32>,
        life_cycle_state: ManifestSmallInt<u32>,
    }, ManifestUsageConstraints
}

#[derive(Clone, Default, Deserialize, Serialize, Debug)]
pub struct ManifestExtTableEntryDef {
    identifier: ManifestSmallInt<u32>,
    offset: ManifestSmallInt<u32>,
}

impl TryFrom<ManifestSpxSignature> for SigverifySpxSignature {
    type Error = anyhow::Error;

    fn try_from(spx_signature: ManifestSpxSignature) -> Result<SigverifySpxSignature> {
        if spx_signature.eq(&ManifestSpxSignature::from_le_bytes([0])?) {
            // In the case where the BigInt fields are defined but == 0 we should just keep it 0.
            // Without this the conversion to [u32; 8] would fail.
            Ok(SigverifySpxSignature {
                data: le_slice_to_arr(&[0]),
            })
        } else {
            // Convert between the BigInt byte representation and the manifest word representation.
            Ok(SigverifySpxSignature {
                data: le_slice_to_arr(
                    spx_signature
                        .to_le_bytes()
                        .chunks(4)
                        .map(|v| Ok(u32::from_le_bytes(le_slice_to_arr(v))))
                        .collect::<Result<Vec<u32>>>()?
                        .as_slice(),
                ),
            })
        }
    }
}

impl TryFrom<ManifestSpxKey> for SigverifySpxKey {
    type Error = anyhow::Error;

    fn try_from(spx_key: ManifestSpxKey) -> Result<SigverifySpxKey> {
        if spx_key.eq(&ManifestSpxKey::from_le_bytes([0])?) {
            // In the case where the BigInt fields are defined but == 0 we should just keep it 0.
            // Without this the conversion to [u32; 8] would fail.
            Ok(SigverifySpxKey {
                data: le_slice_to_arr(&[0]),
            })
        } else {
            // Convert between the BigInt byte representation and the manifest word representation.
            Ok(SigverifySpxKey {
                data: le_slice_to_arr(
                    spx_key
                        .to_le_bytes()
                        .chunks(4)
                        .map(|v| Ok(u32::from_le_bytes(le_slice_to_arr(v))))
                        .collect::<Result<Vec<u32>>>()?
                        .as_slice(),
                ),
            })
        }
    }
}

impl TryFrom<ManifestRsaBuffer> for SigverifyRsaBuffer {
    type Error = anyhow::Error;

    fn try_from(rsa: ManifestRsaBuffer) -> Result<SigverifyRsaBuffer> {
        if rsa.eq(&ManifestRsaBuffer::from_le_bytes([0])?) {
            // In the case where the BigInt fields are defined but == 0 we should just keep it 0.
            // Without this the conversion to [u32; 96] would fail.
            Ok(SigverifyRsaBuffer {
                data: le_slice_to_arr(&[0]),
            })
        } else {
            // Convert between the BigInt byte representation and the manifest word representation.
            Ok(SigverifyRsaBuffer {
                data: le_slice_to_arr(
                    rsa.to_le_bytes()
                        .chunks(4)
                        .map(|v| Ok(u32::from_le_bytes(le_slice_to_arr(v))))
                        .collect::<Result<Vec<u32>>>()?
                        .as_slice(),
                ),
            })
        }
    }
}

/// Takes a slice with LE element ordering and pads the MSBs with 0 to produce a fixed length array
///
/// This is similar to using `try_into()` but does not have the requirement that the slice has
/// exactly the correct length.
fn le_slice_to_arr<T: Default + Copy, const N: usize>(slice: &[T]) -> [T; N] {
    let mut arr = [T::default(); N];
    arr[..slice.len()].copy_from_slice(slice);
    arr
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

impl TryFrom<[u32; 2]> for Timestamp {
    type Error = anyhow::Error;

    fn try_from(words: [u32; 2]) -> Result<Timestamp> {
        Ok(Timestamp { data: words })
    }
}

impl TryFrom<[u32; 8]> for LifecycleDeviceId {
    type Error = anyhow::Error;

    fn try_from(words: [u32; 8]) -> Result<LifecycleDeviceId> {
        Ok(LifecycleDeviceId { device_id: words })
    }
}

impl TryFrom<SigverifySpxSignature> for ManifestSpxSignatureBigInt {
    type Error = anyhow::Error;

    fn try_from(o: SigverifySpxSignature) -> Result<ManifestSpxSignatureBigInt> {
        (&o).try_into()
    }
}

impl TryFrom<&SigverifySpxSignature> for ManifestSpxSignatureBigInt {
    type Error = anyhow::Error;

    fn try_from(o: &SigverifySpxSignature) -> Result<ManifestSpxSignatureBigInt> {
        let spx_signature = ManifestSpxSignature::from_le_bytes(o.data.as_bytes())?;
        Ok(ManifestSpxSignatureBigInt(Some(HexEncoded(spx_signature))))
    }
}

impl TryFrom<SigverifySpxKey> for ManifestSpxKeyBigInt {
    type Error = anyhow::Error;

    fn try_from(o: SigverifySpxKey) -> Result<ManifestSpxKeyBigInt> {
        (&o).try_into()
    }
}

impl TryFrom<&SigverifySpxKey> for ManifestSpxKeyBigInt {
    type Error = anyhow::Error;

    fn try_from(o: &SigverifySpxKey) -> Result<ManifestSpxKeyBigInt> {
        let spx_key = ManifestSpxKey::from_le_bytes(o.data.as_bytes())?;
        Ok(ManifestSpxKeyBigInt(Some(HexEncoded(spx_key))))
    }
}

impl TryFrom<SigverifyRsaBuffer> for ManifestRsaBigInt {
    type Error = anyhow::Error;

    fn try_from(o: SigverifyRsaBuffer) -> Result<ManifestRsaBigInt> {
        (&o).try_into()
    }
}

impl TryFrom<&SigverifyRsaBuffer> for ManifestRsaBigInt {
    type Error = anyhow::Error;

    fn try_from(o: &SigverifyRsaBuffer) -> Result<ManifestRsaBigInt> {
        let rsa = ManifestRsaBuffer::from_le_bytes(o.data.as_bytes())?;
        Ok(ManifestRsaBigInt(Some(HexEncoded(rsa))))
    }
}

impl<T> From<&T> for ManifestSmallInt<T>
where
    T: ParseInt + fmt::LowerHex + Copy,
{
    fn from(o: &T) -> ManifestSmallInt<T> {
        ManifestSmallInt(Some(HexEncoded(*o)))
    }
}

impl From<&KeymgrBindingValue> for [ManifestSmallInt<u32>; 8] {
    fn from(o: &KeymgrBindingValue) -> [ManifestSmallInt<u32>; 8] {
        o.data.map(|v| ManifestSmallInt(Some(HexEncoded(v))))
    }
}
impl From<&Timestamp> for [ManifestSmallInt<u32>; 2] {
    fn from(o: &Timestamp) -> [ManifestSmallInt<u32>; 2] {
        o.data.map(|v| ManifestSmallInt(Some(HexEncoded(v))))
    }
}

impl From<&LifecycleDeviceId> for [ManifestSmallInt<u32>; 8] {
    fn from(o: &LifecycleDeviceId) -> [ManifestSmallInt<u32>; 8] {
        o.device_id.map(|v| ManifestSmallInt(Some(HexEncoded(v))))
    }
}

impl From<&ManifestExtTableEntry> for ManifestExtTableEntryDef {
    fn from(o: &ManifestExtTableEntry) -> ManifestExtTableEntryDef {
        ManifestExtTableEntryDef {
            identifier: ManifestSmallInt(Some(HexEncoded(o.identifier))),
            offset: ManifestSmallInt(Some(HexEncoded(o.offset))),
        }
    }
}

impl From<[ManifestExtTableEntry; 8]> for ManifestExtTable {
    fn from(o: [ManifestExtTableEntry; 8]) -> ManifestExtTable {
        ManifestExtTable { entries: o }
    }
}

impl From<&ManifestExtTable> for [ManifestExtTableEntryDef; 8] {
    fn from(o: &ManifestExtTable) -> [ManifestExtTableEntryDef; 8] {
        o.entries.map(|v| (&v).into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;
    use deser_hjson::from_str;

    #[test]
    fn test_manifest_from_hjson() {
        let def: ManifestSpec =
            from_str(&std::fs::read_to_string(testdata!("manifest.hjson")).unwrap()).unwrap();

        let _: Manifest = def.try_into().unwrap();
    }

    #[test]
    fn test_manifest_from_hjson_missing() {
        let def: ManifestSpec =
            from_str(&std::fs::read_to_string(testdata!("manifest_missing.hjson")).unwrap())
                .unwrap();

        let res: Result<Manifest> = def.try_into();
        assert!(res.is_err())
    }

    #[test]
    fn test_manifest_overwrite() {
        let mut base: ManifestSpec =
            from_str(&std::fs::read_to_string(testdata!("manifest.hjson")).unwrap()).unwrap();
        let other = ManifestSpec {
            identifier: from_str("0xabcd").unwrap(),
            binding_value: from_str(stringify!(["0", "1", "2", "3", "4", "5", "6", "7"])).unwrap(),
            ..Default::default()
        };
        base.overwrite(other);
        assert_eq!(base.identifier.0.unwrap().0, 0xabcd);
        assert_eq!(
            base.binding_value.map(|v| v.0.unwrap().0)[..],
            [0, 1, 2, 3, 4, 5, 6, 7]
        );

        // Ensure unspecified fields are not overwritten.
        assert_eq!(base.address_translation.0.unwrap().0, 0x739);
    }

    #[test]
    fn test_manifest_convert() {
        let def1: ManifestSpec =
            from_str(&std::fs::read_to_string(testdata!("manifest.hjson")).unwrap()).unwrap();
        let def2 = def1.clone();

        let bin1: Manifest = def1.try_into().unwrap();
        let bin2: Manifest = def2.try_into().unwrap();

        let redef: ManifestSpec = (&bin1).try_into().unwrap();
        let rebin: Manifest = redef.try_into().unwrap();
        assert_eq!(bin2.as_bytes(), rebin.as_bytes());
    }
}
