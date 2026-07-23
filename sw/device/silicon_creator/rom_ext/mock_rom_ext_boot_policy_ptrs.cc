// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/mock_rom_ext_boot_policy_ptrs.h"

namespace rom_test {
extern "C" {
const manifest_t *rom_ext_boot_policy_manifest_a_get(
    const boot_data_t *boot_data) {
  return MockRomExtBootPolicyPtrs::Instance().ManifestA(boot_data);
}

const manifest_t *rom_ext_boot_policy_manifest_b_get(
    const boot_data_t *boot_data) {
  return MockRomExtBootPolicyPtrs::Instance().ManifestB(boot_data);
}
}  // extern "C"
}  // namespace rom_test
