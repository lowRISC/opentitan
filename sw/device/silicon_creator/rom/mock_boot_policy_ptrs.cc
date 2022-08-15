// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/mock_boot_policy_ptrs.h"

namespace rom_test {
extern "C" {
const manifest_t *boot_policy_manifest_a_get() {
  return MockBootPolicyPtrs::Instance().ManifestA();
}

const manifest_t *boot_policy_manifest_b_get() {
  return MockBootPolicyPtrs::Instance().ManifestB();
}
}  // extern "C"
}  // namespace rom_test
