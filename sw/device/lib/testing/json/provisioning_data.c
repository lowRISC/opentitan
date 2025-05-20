// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/testing/json/provisioning_data.h"

/**
 * Max sizes of the UJSON structs below when they are serialized.
 *
 * The are obtained by running the following FPGA test:
 * bazel test --test_output=streamed \
 *  //sw/device/silicon_creator/manuf/tests:ujson_msg_size_functest
 */
enum {
  kSerdesSha256HashSerializedMaxSize = 98,
  kLcTokenHashSerializedMaxSize = 52,
  kManufCertgenInputsSerializedMaxSize = 210,
  kPersoBlobSerializedMaxSize = 20535,
};
