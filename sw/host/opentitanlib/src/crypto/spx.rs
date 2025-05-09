// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, ensure, Context, Result};
use pem_rfc7468::Decoder;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use super::Error;
use crate::crypto::utils;
use sphincsplus::{DecodeKey, SpxPublicKey};

#[derive(Debug, Serialize, Deserialize, Annotate)]
pub struct SpxRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub key: Vec<u8>,
}

impl Default for SpxRawPublicKey {
    fn default() -> Self {
        Self { key: vec![0; 32] }
    }
}

impl TryFrom<&sphincsplus::SpxPublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: &SpxPublicKey) -> Result<Self, Self::Error> {
        Ok(Self {
            key: v.as_bytes().to_vec(),
        })
    }
}

impl TryFrom<sphincsplus::SpxPublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: SpxPublicKey) -> Result<Self, Self::Error> {
        (&v).try_into()
    }
}

impl FromStr for SpxRawPublicKey {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let key = SpxPublicKey::read_pem_file(s)
            .with_context(|| format!("Failed to load {s}"))
            .map_err(Error::Other)?;
        SpxRawPublicKey::try_from(&key)
    }
}

impl SpxRawPublicKey {
    pub const SIZE: usize = 32;
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut key = Self::default();
        key.key.resize(32, 0);
        src.read_exact(&mut key.key)?;
        Ok(key)
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.key.len() == Self::SIZE,
            Error::InvalidPublicKey(anyhow!("bad key length: {}", self.key.len()))
        );
        dest.write_all(&self.key)?;
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Annotate)]
pub struct SpxRawSignature {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub raw_data: Vec<u8>,
}

impl Default for SpxRawSignature {
    fn default() -> Self {
        Self {
            raw_data: vec![0u8; 7856],
        }
    }
}

impl TryFrom<&[u8]> for SpxRawSignature {
    type Error = Error;
    fn try_from(value: &[u8]) -> std::result::Result<Self, Self::Error> {
        if value.len() != Self::SIZE {
            return Err(Error::InvalidSignature(anyhow!(
                "bad length: {}",
                value.len()
            )));
        }
        let mut value = std::io::Cursor::new(value);
        SpxRawSignature::read(&mut value).map_err(Error::InvalidSignature)
    }
}

impl SpxRawSignature {
    const SIZE: usize = 7856;

    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut sig = Self::default();
        src.read_exact(&mut sig.raw_data)?;
        Ok(sig)
    }

    pub fn read_from_file(path: &Path) -> Result<SpxRawSignature> {
        let mut file =
            File::open(path).with_context(|| format!("Failed to read file: {path:?}"))?;
        let file_size = std::fs::metadata(path)
            .with_context(|| format!("Failed to get metadata for {path:?}"))?
            .len();

        let raw_size = Self::SIZE as u64;
        if file_size == raw_size {
            // This must be a raw signature, just read it as is.
            SpxRawSignature::read(&mut file)
        } else {
            let mut data = Vec::<u8>::new();

            file.read_to_end(&mut data)
                .with_context(|| "Failed to read {path:?}")?;

            // Try parsing as PEM decoding.
            SpxRawSignature::from_pem(&data).with_context(|| format!("Failed parsing {path:?}"))
        }
    }

    fn from_pem(data: &[u8]) -> Result<SpxRawSignature> {
        // Ensures valid PEM markers and a recognized label are present.
        let _ = pem_rfc7468::decode_label(data)?;
        let mut raw_data = Vec::new();
        let result = Decoder::new(data);
        match result {
            Ok(mut decoder) => decoder.decode_to_end(&mut raw_data)?,
            _ => {
                let cleaned_data = utils::clean_pem_bytes_for_parsing(data)?;
                let mut decoder = Decoder::new(&cleaned_data)?;
                decoder.decode_to_end(&mut raw_data)?
            }
        };
        Ok(SpxRawSignature { raw_data })
    }
}
