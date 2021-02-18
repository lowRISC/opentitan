// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

use crate::manifest;
use rom_ext_config::parser::ParsedConfig;

/// Stripped binary image buffer.
pub struct RawImage {
    data: Vec<u8>,
    path: PathBuf,
}

/// Buffer manipulation API.
impl RawImage {
    /// Creates the new image buffer.
    ///
    /// The data is read from the requested raw binary file.
    pub fn new(image_path: &Path) -> Self {
        let data = fs::read(image_path).expect("Failed to read the image!");

        RawImage {
            data: data,
            path: image_path.to_path_buf(),
        }
    }

    /// Updates the manifest portion of the image buffer.
    ///
    /// This function updates the image manifest data with values parsed
    /// from configuration file.
    pub fn update_generic_fields(&mut self, config: &ParsedConfig) {
        // TODO checks to make sure that the config values (strings) are not
        // bigger than the actual field size.

        let mut myclosure = |value, offset| {
            let bytes = str_to_vec_u8(value);
            let data = &mut self.data;
            let begin = offset as usize;
            let end = begin + bytes.len();
            data.splice(begin..end, bytes.iter().cloned());
        };

        myclosure(
            &config.manifest_identifier,
            manifest::ROM_EXT_MANIFEST_IDENTIFIER_OFFSET,
        );
        myclosure(&config.image_length, manifest::ROM_EXT_IMAGE_LENGTH_OFFSET);
        myclosure(
            &config.image_version,
            manifest::ROM_EXT_IMAGE_VERSION_OFFSET,
        );
        myclosure(
            &config.image_timestamp,
            manifest::ROM_EXT_IMAGE_TIMESTAMP_OFFSET,
        );
        myclosure(
            &config.extension0_checksum,
            manifest::ROM_EXT_EXTENSION0_CHECKSUM_OFFSET,
        );
        myclosure(
            &config.extension1_checksum,
            manifest::ROM_EXT_EXTENSION1_CHECKSUM_OFFSET,
        );
        myclosure(
            &config.extension2_checksum,
            manifest::ROM_EXT_EXTENSION2_CHECKSUM_OFFSET,
        );
        myclosure(
            &config.extension3_checksum,
            manifest::ROM_EXT_EXTENSION3_CHECKSUM_OFFSET,
        );
    }

    /// Writes the image buffer contents into a file.
    ///
    /// Places the new file alongside the original, with a "new_" prefix.
    pub fn write_file(&self) {
        let file_name = self.path.file_name().expect("Failed to get file stem!");

        let mut new_file_name = OsString::from("new_");
        new_file_name.push(file_name);

        let output_file = self.path.with_file_name(new_file_name);

        fs::write(output_file, &self.data).expect("Failed to write the new binary file!");
    }
}

/// Converts hex/decimal uint string into a little endian byte vector.
///
/// Note: only understands unsigned u64 and u32 integers.
fn str_to_vec_u8(s: &str) -> Vec<u8> {
    let value = match s.starts_with("0x") {
        true => u64::from_str_radix(s.trim_start_matches("0x"), 16)
            .expect("Failed to parse string to u64!"),
        false => s.parse::<u64>().expect("Failed to parse string to u64!"),
    };

    if value <= (u32::MAX as u64) {
        (value as u32).to_le_bytes().to_vec()
    } else {
        value.to_le_bytes().to_vec()
    }
}
