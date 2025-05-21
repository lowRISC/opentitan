// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use indexmap::IndexMap;

pub mod provisioning_data;

/// Max sizes of the UJSON structs below when they are serialized.
///
/// The are obtained by running the following FPGA test:
/// bazel test --test_output=streamed \
///  //sw/device/silicon_creator/manuf/tests:ujson_msg_size_functest
pub const SERDES_SHA256_HASH_SERIALIZED_MAX_SIZE: usize = 98;
pub const LC_TOKEN_HASH_SERIALIZED_MAX_SIZE: usize = 52;
pub const MANUF_CERTGEN_INPUTS_SERIALIZED_MAX_SIZE: usize = 210;
pub const PERSO_BLOB_SERIALIZED_MAX_SIZE: usize = 20535;

pub struct UjsonPayloads {
    /// HashMap of "Name" --> "UJSON data" sent from the Host to the Device
    /// during provisioning.
    pub dut_in: IndexMap<String, String>,
}
