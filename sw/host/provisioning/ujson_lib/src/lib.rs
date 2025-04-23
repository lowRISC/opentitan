// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;

pub mod provisioning_data;

#[derive(Debug)] // Often useful for printing and debugging
pub struct UjsonString {
    pub string: String,
    pub dynamic_data_offsets: Vec<usize>,
    pub dynamic_data_lengths: Vec<usize>,
}

pub struct UjsonPayloads {
    /// HashMap of "Name" --> "UJSON data" sent from the Host to the Device
    /// during provisioning.
    pub dut_in: IndexMap<String, UjsonString>,
}
