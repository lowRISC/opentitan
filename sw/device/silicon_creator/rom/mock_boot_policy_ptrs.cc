// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/mock_boot_policy_ptrs.h"

namespace rom_test {
extern "C" {
const manifest_t *boot_policy_manifest_a_load() {
  return MockBootPolicyPtrs::Instance().LoadManifestA();
}

const manifest_t *boot_policy_manifest_b_load() {
  return MockBootPolicyPtrs::Instance().LoadManifestB();
}

void boot_policy_manifest_a_unload() {
  MockBootPolicyPtrs::Instance().UnloadManifestA();
}

void boot_policy_manifest_b_unload() {
  MockBootPolicyPtrs::Instance().UnloadManifestB();
}
}  // extern "C"
}  // namespace rom_test
