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
    }

    /// Updates ROM_EXT manifest timestamp field.
    ///
    /// The generated time stamp is u64. Normally time stamp is a signed
    /// integer, however there is no risk of overflow into a "negative".
    pub fn update_timestamp_field(&mut self) {
        let duration = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("Failed to obtain the current time!");

        let bytes = duration.as_secs().to_le_bytes();
        self.update_field(&bytes, manifest::ROM_EXT_IMAGE_TIMESTAMP_OFFSET);
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
        self.update_field(
            modulus,
            manifest::ROM_EXT_SIGNATURE_KEY_MODULUS_OFFSET,
        );
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
        let file_name =
            self.path.file_name().expect("Failed to get file stem!");

        let mut new_file_name = OsString::from("new_");
        new_file_name.push(file_name);

        let output_file = self.path.with_file_name(new_file_name);

        fs::write(output_file, &self.data)
            .expect("Failed to write the new binary file!");
    }

    /// Updates ROM_EXT manifest usage constraints field.
    fn update_usage_constraints_field(&mut self, path: &Path) {
        // Update fields from config.
        let usage_constraints =
            fs::read(path).expect("Failed to read usage constraints!");
        self.update_field(
            &usage_constraints,
            manifest::ROM_EXT_USAGE_CONSTRAINTS_OFFSET,
        );
    }

    /// Updates ROM_EXT manifest peripheral lockdown info field.
    ///
    /// The information is encoded into the 128-bit binary blob.
    fn update_peripheral_lockdown_info_field(
        &mut self,
        _info: &PeripheralLockdownInfo,
    ) {
        // TODO: generate the peripheral_lockdown_blob from
        //       PeripheralLockdownInfo, meanwhile use a hard-coded vector.

        self.update_field(
            &[0xA5; 16],
            manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET,
        );
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

fn str_to_u64(val: &str) -> u64 {
    match val.strip_prefix("0x") {
        Some(s) => u64::from_str_radix(s, 16),
        None => u64::from_str_radix(val, 10),
    }
    .expect("Failed to parse string to u64!")
}

/// Converts hex/decimal uint string into a little endian byte vector.
///
/// Note: only understands values up to u64::MAX.
fn str_to_vec_u8(s: &str) -> Vec<u8> {
    match str_to_u64(s).to_le_bytes() {
        [a, b, c, d, 0, 0, 0, 0] => vec![a, b, c, d],
        bytes => bytes.to_vec(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::HashMap;
    use std::env;

    use rom_ext_config::parser::Extension;
    use rom_ext_config::parser::InputFiles;

    static DEV_RELATIVE_PATH: &str = "sw/host/rom_ext_image_tools/signer/dev";

    #[test]
    fn test_update_static_fields() {
        let source_root = env::var("MESON_SOURCE_ROOT")
            .expect("Failed, ENV variable not set!");

        let dev_path = Path::new(&source_root).join(DEV_RELATIVE_PATH);
        let full_path = |path| dev_path.join(path);

        let config = ParsedConfig {
            input_files: InputFiles {
                image_path: full_path("rom_ext_blank_image.bin"),
                private_key_der_path: PathBuf::from(""),
                usage_constraints_path: full_path("usage_constraints.bin"),
                system_state_value_path: PathBuf::from(""),
            },
            peripheral_lockdown_info: PeripheralLockdownInfo { value: 0 },
            manifest_identifier: String::from("0x11111111"),
            image_version: String::from("0x22222222"),
            extensions: [
                Extension {
                    offset: String::from("0x33333333"),
                    checksum: String::from("0x44444444"),
                },
                Extension {
                    offset: String::from("0x55555555"),
                    checksum: String::from("0x55555555"),
                },
                Extension {
                    offset: String::from("0x66666666"),
                    checksum: String::from("0x66666666"),
                },
                Extension {
                    offset: String::from("0x77777777"),
                    checksum: String::from("0x77777777"),
                },
            ],
        };

        let mut test_items: HashMap<usize, Vec<u8>> = HashMap::new();

        let mut add_test_item = |key, val: Vec<u8>, expected_size| {
            assert_eq!(val.len(), expected_size as usize);
            test_items.insert(key as usize, val);
        };

        add_test_item(
            manifest::ROM_EXT_MANIFEST_IDENTIFIER_OFFSET,
            str_to_vec_u8(&config.manifest_identifier),
            manifest::ROM_EXT_MANIFEST_IDENTIFIER_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_IMAGE_VERSION_OFFSET,
            str_to_vec_u8(&config.image_version),
            manifest::ROM_EXT_IMAGE_VERSION_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION0_OFFSET_OFFSET,
            str_to_vec_u8(&config.extensions[0].offset),
            manifest::ROM_EXT_EXTENSION0_OFFSET_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION1_OFFSET_OFFSET,
            str_to_vec_u8(&config.extensions[1].offset),
            manifest::ROM_EXT_EXTENSION1_OFFSET_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION2_OFFSET_OFFSET,
            str_to_vec_u8(&config.extensions[2].offset),
            manifest::ROM_EXT_EXTENSION2_OFFSET_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION3_OFFSET_OFFSET,
            str_to_vec_u8(&config.extensions[3].offset),
            manifest::ROM_EXT_EXTENSION3_OFFSET_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION0_CHECKSUM_OFFSET,
            str_to_vec_u8(&config.extensions[0].checksum),
            manifest::ROM_EXT_EXTENSION0_CHECKSUM_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION1_CHECKSUM_OFFSET,
            str_to_vec_u8(&config.extensions[1].checksum),
            manifest::ROM_EXT_EXTENSION1_CHECKSUM_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION2_CHECKSUM_OFFSET,
            str_to_vec_u8(&config.extensions[2].checksum),
            manifest::ROM_EXT_EXTENSION2_CHECKSUM_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_EXTENSION3_CHECKSUM_OFFSET,
            str_to_vec_u8(&config.extensions[3].checksum),
            manifest::ROM_EXT_EXTENSION3_CHECKSUM_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_USAGE_CONSTRAINTS_OFFSET,
            fs::read(&config.input_files.usage_constraints_path)
                .expect("Failed to read usage constraints!"),
            manifest::ROM_EXT_USAGE_CONSTRAINTS_SIZE_BYTES,
        );
        add_test_item(
            manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET,
            [0xA5; 16].to_vec(),
            manifest::ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_BYTES,
        );

        let mut image = RawImage::new(&config.input_files.image_path);

        // Make sure that the image is blank to start with.
        assert_eq!(image.data, vec![0; image.data.len()]);

        image.update_static_fields(&config);

        // Iterate through every single byte in the image, if it belongs to a
        // field under test - compare with the respective `test_tuple` field,
        // otherwise it should be zero.
        let mut i = 0;
        while i < image.data.len() {
            // Check if the byte is part of the fields under test.
            match test_items.get(&i) {
                Some(x) => {
                    // Check that field under test was successfully written
                    // to the image.
                    for byte in x {
                        assert_eq!(*byte, image.data[i], "index = {}", i);
                        i += 1;
                    }
                }
                _ => {
                    // Make sure that any other bytes are zero.
                    assert_eq!(image.data[i], 0, "index = {}", i);
                    i += 1;
                }
            }
        }
    }
}
