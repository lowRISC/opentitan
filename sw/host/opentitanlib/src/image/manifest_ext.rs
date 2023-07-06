// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{self, Deserialize, Serialize};
use std::path::{Path, PathBuf};
use thiserror::Error;
use zerocopy::AsBytes;

use crate::crypto::spx::{self, SpxPublicKeyPart};
use crate::image::manifest::*;
use crate::image::manifest_def::le_bytes_to_word_arr;
use crate::util::file::FromReader;
use crate::util::num_de::HexEncoded;
use crate::with_unknown;

#[derive(Debug, Error)]
pub enum ManifestExtError {
    #[error("Extension ID 0x{0:x} has duplicate extension data.")]
    DuplicateEntry(u32),
}

with_unknown! {
    /// Known manifest extension variant IDs.
    #[derive(Default)]
    pub enum ManifestExtId: u32 {
        spx_key = MANIFEST_EXT_ID_SPX_KEY,
        spx_signature = MANIFEST_EXT_ID_SPX_SIGNATURE,
    }
}

/// Top level spec for manifest extension HJSON files.
#[derive(Default, Debug, Deserialize, Serialize)]
pub struct ManifestExtSpec {
    pub signed_region: Vec<ManifestExtEntrySpec>,
    pub unsigned_region: Vec<ManifestExtEntrySpec>,
    #[serde(skip)]
    relative_path: Option<PathBuf>,
}

/// Specs for the known extension variants.
///
/// This includes a raw variant that can take any id, name, and value.
#[derive(Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub enum ManifestExtEntrySpec {
    SpxKey {
        /// The path to the SPHINCS+ public or private key.
        ///
        /// If a relative path is used, this path will typically be resolved relative to the path
        /// given by `ManifestExtSpc::source_path()` of the `ManifestExtSpec` that contains this
        /// spec.
        spx_key: PathBuf,
    },
    SpxSignature {
        /// The path to the SPHINCS+ signature.
        ///
        /// If a relative path is used, this path will typically be resolved relative to the path
        /// given by `ManifestExtSpc::source_path()` of the `ManifestExtSpec` that contains this
        /// spec.
        spx_signature: PathBuf,
    },
    Raw {
        name: HexEncoded<u32>,
        identifier: HexEncoded<u32>,
        value: Vec<HexEncoded<u8>>,
    },
}

#[derive(Debug)]
pub enum ManifestExtEntry {
    SpxKey(ManifestExtSpxKey),
    SpxSignature(Box<ManifestExtSpxSignature>),
    Raw {
        header: ManifestExtHeader,
        data: Vec<u8>,
    },
}

impl ManifestExtSpec {
    /// Reads in a `ManifestExtSpec` from an HJSON file.
    ///
    /// The parent of `path` (the directory containing the HJSON file to be loaded) is used when
    /// resolving relative paths for any extension data that references a file.
    pub fn read_from_file(path: &Path) -> Result<Self> {
        let mut spec: Self = deser_hjson::from_str(&std::fs::read_to_string(path)?)?;
        spec.relative_path = path.parent().map(|v| v.to_owned());
        Ok(spec)
    }

    /// The partent of the path that was provided when loading this spec.
    pub fn source_path(&self) -> Option<&Path> {
        self.relative_path.as_deref()
    }
}

impl ManifestExtEntrySpec {
    pub fn id(&self) -> u32 {
        match self {
            ManifestExtEntrySpec::SpxKey { spx_key: _ } => MANIFEST_EXT_ID_SPX_KEY,
            ManifestExtEntrySpec::SpxSignature { spx_signature: _ } => {
                MANIFEST_EXT_ID_SPX_SIGNATURE
            }
            ManifestExtEntrySpec::Raw {
                name: _,
                identifier,
                value: _,
            } => **identifier,
        }
    }
}

impl ManifestExtEntry {
    /// Creates a new manifest extension from a given SPHINCS+ `key`.
    pub fn new_spx_key_entry(key: &spx::SpxKey) -> Result<Self> {
        Ok(ManifestExtEntry::SpxKey(ManifestExtSpxKey {
            header: ManifestExtHeader {
                identifier: MANIFEST_EXT_ID_SPX_KEY,
                name: MANIFEST_EXT_NAME_SPX_KEY,
            },
            key: SigverifySpxKey {
                data: le_bytes_to_word_arr(key.pk_as_bytes())?,
            },
        }))
    }

    /// Creates a new manifest extension from a given SPHINCS+ `signature`.
    pub fn new_spx_signature_entry(signature: &spx::SpxSignature) -> Result<Self> {
        Ok(ManifestExtEntry::SpxSignature(Box::new(
            ManifestExtSpxSignature {
                header: ManifestExtHeader {
                    identifier: MANIFEST_EXT_ID_SPX_SIGNATURE,
                    name: MANIFEST_EXT_NAME_SPX_SIGNATURE,
                },
                signature: SigverifySpxSignature {
                    data: le_bytes_to_word_arr(&signature.0.to_le_bytes())?,
                },
            },
        )))
    }

    /// Creates a new manifest extension from a given `spec`.
    ///
    /// For extensions that reference other resources, such as SPHINCS+ keys or signatures, this
    /// function will attempt to load those resources to create the extension.
    pub fn from_spec(spec: &ManifestExtEntrySpec, relative_path: Option<&Path>) -> Result<Self> {
        let relative_path = relative_path.unwrap_or(Path::new(""));
        Ok(match spec {
            ManifestExtEntrySpec::SpxKey { spx_key } => ManifestExtEntry::new_spx_key_entry(
                &spx::load_spx_key(&relative_path.join(spx_key))?,
            )?,
            ManifestExtEntrySpec::SpxSignature { spx_signature } => {
                ManifestExtEntry::new_spx_signature_entry(&spx::SpxSignature::read_from_file(
                    &relative_path.join(spx_signature),
                )?)?
            }
            ManifestExtEntrySpec::Raw {
                name,
                identifier,
                value,
            } => ManifestExtEntry::Raw {
                header: ManifestExtHeader {
                    identifier: **identifier,
                    name: **name,
                },
                data: value.iter().map(|v| **v).collect(),
            },
        })
    }

    /// Returns the header portion of this extension.
    pub fn header(&self) -> &ManifestExtHeader {
        match self {
            ManifestExtEntry::SpxKey(key) => &key.header,
            ManifestExtEntry::SpxSignature(sig) => &sig.header,
            ManifestExtEntry::Raw { header, data: _ } => header,
        }
    }

    /// Allocates a new byte `Vec<u8>` and writes the binary extension data to it.
    pub fn to_vec(&self) -> Vec<u8> {
        match self {
            ManifestExtEntry::SpxKey(key) => key.as_bytes().to_vec(),
            ManifestExtEntry::SpxSignature(sig) => sig.as_bytes().to_vec(),
            ManifestExtEntry::Raw { header, data } => {
                header.as_bytes().iter().chain(data).copied().collect()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;
    use crate::util::num_de::HexEncoded;

    #[test]
    fn test_manifest_ext_from_hjson() {
        let spec = ManifestExtSpec::read_from_file(&testdata!("manifest_ext.hjson")).unwrap();
        assert_eq!(spec.source_path(), Some(testdata!().as_path()));
        assert_eq!(spec.signed_region.len(), 2);
        assert_eq!(
            spec.signed_region[0],
            ManifestExtEntrySpec::SpxKey {
                spx_key: "test_spx.pem".into()
            }
        );
        assert_eq!(
            spec.signed_region[1],
            ManifestExtEntrySpec::Raw {
                name: HexEncoded(0xbeef),
                identifier: HexEncoded(0xabcd),
                value: [0x01, 0x23, 0x45, 0x67].map(HexEncoded).to_vec()
            }
        );
        assert_eq!(spec.unsigned_region.len(), 1);
        assert_eq!(
            spec.unsigned_region[0],
            ManifestExtEntrySpec::SpxSignature {
                spx_signature: "test_signature.bin".into()
            }
        );
    }
}
