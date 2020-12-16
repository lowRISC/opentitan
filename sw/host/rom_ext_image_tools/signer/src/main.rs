// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::env;
use std::path;

use rom_ext_config::parser;

fn main() {
    let args: Vec<String> = env::args().collect();

    let config_path = path::Path::new(&args[1]);

    // Parse the config.
    let _config = parser::ParsedConfig::new(&config_path);
}
