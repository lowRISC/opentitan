// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use pem_rfc7468::Decoder;
use std::fs::File;
use std::io::Read;
use std::path::Path;

use crate::{SphincsPlus, SpxError};
use util::clean_pem_bytes_for_parsing;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SpxRawSignature {
    raw_data: Vec<u8>,
}

impl SpxRawSignature {
    pub fn read(src: &mut impl Read, algorithm: SphincsPlus) -> Result<Self, SpxError> {
        let mut raw_data = vec![0; algorithm.signature_len()];
        src.read_exact(&mut raw_data)?;
        Ok(SpxRawSignature { raw_data })
    }

    pub fn read_from_file(path: &Path, algorithm: SphincsPlus) -> Result<Self, SpxError> {
        let mut file = File::open(path)?;
        let file_size = std::fs::metadata(path)?.len() as usize;

        if file_size == algorithm.signature_len() {
            // This must be a raw signature, just read it as is.
            SpxRawSignature::read(&mut file, algorithm)
        } else {
            let mut data = Vec::<u8>::new();

            file.read_to_end(&mut data)?;

            // Try parsing as PEM decoding.
            SpxRawSignature::from_pem(&data, algorithm)
        }
    }

    fn from_pem(data: &[u8], algorithm: SphincsPlus) -> Result<Self, SpxError> {
        // Ensures valid PEM markers and a recognized label are present.
        let _ = pem_rfc7468::decode_label(data)?;
        let mut raw_data = Vec::new();
        let result = Decoder::new(data);
        match result {
            Ok(mut decoder) => decoder.decode_to_end(&mut raw_data)?,
            _ => {
                let cleaned_data = clean_pem_bytes_for_parsing(data)?;
                let mut decoder = Decoder::new(&cleaned_data)?;
                decoder.decode_to_end(&mut raw_data)?
            }
        };
        if algorithm.signature_len() != raw_data.len() {
            return Err(SpxError::BadSigLength(raw_data.len()));
        }
        Ok(SpxRawSignature { raw_data })
    }

    /// Returns the raw signature bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.raw_data.as_slice()
    }
}
