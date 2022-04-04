// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"

namespace mask_rom_test {
extern "C" {
const manifest_t *rom_ext_boot_policy_manifest_a_get() {
  return MockRomExtBootPolicyPtrs::Instance().ManifestA();
}

const manifest_t *rom_ext_boot_policy_manifest_b_get() {
  return MockRomExtBootPolicyPtrs::Instance().ManifestB();
}
}  // extern "C"
}  // namespace mask_rom_test
