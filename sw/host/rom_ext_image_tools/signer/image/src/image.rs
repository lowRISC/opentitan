// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std;
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use crate::manifest;
use rom_ext_config::parser::ParsedConfig;
use rom_ext_config::parser::PeripheralLockdownInfo;

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

    /// Updates the fields from the configuration file.
    ///
    /// This function updates the image manifest data with values parsed from
    /// the configuration file (known ahead of time). Some of the other fields
    /// like signature key public exponent and modulus, are obtained at
    /// run-time.
    pub fn update_static_fields(&mut self, config: &ParsedConfig) {
        // TODO: checks to make sure that the config values (strings) are not
        //       bigger than the actual field size.

        let mut update = |value, offset| {
            let bytes = str_to_vec_u8(value);
            self.update_field(&bytes, offset);
        };

        update(
            &config.manifest_identifier,
            manifest::ROM_EXT_MANIFEST_IDENTIFIER_OFFSET,
        );
        update(
            &config.image_version,
            manifest::ROM_EXT_IMAGE_VERSION_OFFSET,
        );

        let offsets = [
            (
                manifest::ROM_EXT_EXTENSION0_OFFSET_OFFSET,
                manifest::ROM_EXT_EXTENSION0_CHECKSUM_OFFSET,
            ),
            (
                manifest::ROM_EXT_EXTENSION1_OFFSET_OFFSET,
                manifest::ROM_EXT_EXTENSION1_CHECKSUM_OFFSET,
            ),
            (
                manifest::ROM_EXT_EXTENSION2_OFFSET_OFFSET,
                manifest::ROM_EXT_EXTENSION2_CHECKSUM_OFFSET,
            ),
            (
                manifest::ROM_EXT_EXTENSION3_OFFSET_OFFSET,
                manifest::ROM_EXT_EXTENSION3_CHECKSUM_OFFSET,
            ),
        ];
        for (i, offset) in offsets.iter().enumerate() {
            update(&config.extensions[i].offset, offset.0);
            update(&config.extensions[i].checksum, offset.1);
        }

        let usage_constraints_path = &config.input_files.usage_constraints_path;
        self.update_usage_constraints_field(usage_constraints_path);

        let lockdown_info = &config.peripheral_lockdown_info;
        self.update_peripheral_lockdown_info_field(lockdown_info);

        // TODO: calculated at runtime, so we should probably rename this
        //       function.
        self.update_timestamp_field();
    }

    /// Updates ROM_EXT manifest signature key public exponent field.
    pub fn update_exponent_field(&mut self, exponent: &[u8]) {
        self.update_field(
            exponent,
            manifest::ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_OFFSET,
        );
    }

    /// Updates ROM_EXT manifest signature key modulus field.
    pub fn update_modulus_field(&mut self, modulus: &[u8]) {
        self.update_field(modulus, manifest::ROM_EXT_SIGNATURE_KEY_MODULUS_OFFSET);
    }

    /// Updates ROM_EXT manifest signature field.
    pub fn update_signature_field(&mut self, signature: &[u8]) {
        self.update_field(signature, manifest::ROM_EXT_IMAGE_SIGNATURE_OFFSET);
    }

    /// Returns the portion of the image used for signing.
    ///
    /// Manifest identifier and the signature itself are not signed. The rest
    /// of the image, including all the manifest fields that follow the
    /// signature field.
    pub fn data_to_sign(&self) -> &[u8] {
        let offset = manifest::ROM_EXT_SIGNED_AREA_START_OFFSET as usize;
        &self.data[offset..]
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

    /// Updates ROM_EXT manifest usage constraints field.
    fn update_usage_constraints_field(&mut self, path: &Path) {
        // Update fields from config.
        let usage_constraints = fs::read(path).expect("Failed to read usage constraints!");
        self.update_field(
            &usage_constraints,
            manifest::ROM_EXT_USAGE_CONSTRAINTS_OFFSET,
        );
    }

    /// Updates ROM_EXT manifest peripheral lockdown info field.
    ///
    /// The information is encoded into the 128-bit binary blob.
    fn update_peripheral_lockdown_info_field(&mut self, _info: &PeripheralLockdownInfo) {
        // TODO: generate the peripheral_lockdown_blob from
        //       PeripheralLockdownInfo, meanwhile use a hard-coded vector.

        self.update_field(
            &[0xA5; 16],
            manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET,
        );
    }

    /// Updates ROM_EXT manifest timestamp field.
    ///
    /// The generated time stamp is u64. Normally time stamp is a signed
    /// integer, however there is no risk of overflow into a "negative".
    fn update_timestamp_field(&mut self) {
        let duration = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("Failed to obtain the current time!");

        let bytes = &duration.as_secs().to_le_bytes();
        self.update_field(bytes, manifest::ROM_EXT_IMAGE_TIMESTAMP_OFFSET);
    }

    /// Updates a ROM_EXT manifest field.
    ///
    /// Generic function, is used by the specific field update counterparts.
    fn update_field(&mut self, field_data: &[u8], field_offset: u32) {
        let begin = field_offset as usize;
        let end = begin + field_data.len();
        self.data.splice(begin..end, field_data.iter().cloned());
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
