// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Deserialize, Serialize)]
#[serde(untagged)]
pub enum SubstValue {
    ByteArray(Vec<u8>),
    Int32(i32),
}

#[derive(Debug, Deserialize, Serialize)]
pub struct SubstData {
    pub values: HashMap<String, SubstValue>,
}

impl Default for SubstData {
    fn default() -> Self {
        Self::new()
    }
}

impl SubstData {
    pub fn new() -> SubstData {
        SubstData {
            values: HashMap::new(),
        }
    }
}
