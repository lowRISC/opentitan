// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use serde_derive::Deserialize;
use serde_hjson::Value;

/// Configuration used for the manifest initialisation.
#[derive(Deserialize, Debug)]
pub struct ParsedConfig {
    pub input_files: InputFiles,
    pub peripheral_lockdown_info: PeripheralLockdownInfo,
    pub manifest_identifier: String,
    pub image_version: String,
    pub extensions: [Extension; 4],
}

/// Input files that are required for signing.
#[derive(Deserialize, Debug)]
pub struct InputFiles {
    pub image_path: PathBuf,
    pub private_key_der_path: PathBuf,
    pub usage_constraints_path: PathBuf,
    pub system_state_value_path: PathBuf,
}

/// Peripheral Lockdown Information configuration data.
///
/// This data is used to produce 128-bit encoded manifest field.
#[derive(Deserialize, Debug)]
pub struct PeripheralLockdownInfo {
    pub value: u32,
}

/// ROM_EXT.
#[derive(Deserialize, Debug)]
pub struct Extension {
    pub offset: String,
    pub checksum: String,
}

impl ParsedConfig {
    pub fn new(config: &Path) -> Self {
        // Read the entire configuration file.
        let config_data = fs::read_to_string(config).expect("Failed to read the config file!");

        let data: Value =
            serde_hjson::from_str(&config_data).expect("Failed to parse the hjson config file!");

        let deserialized: ParsedConfig =
            serde_hjson::from_value(data).expect("Failed to deserialize hjson config data!");

        deserialized
    }
}
